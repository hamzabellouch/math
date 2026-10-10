import OAI.MathematicalPhysics.RapidForcing.RationalProfiles
import OAI.MathematicalPhysics.RapidForcing.ArithmeticAutomation

namespace OAI

section

open Encodable Denumerable
namespace RapidForcing.EffectiveArithmetic

@[fun_prop] lemma primrec_nat_coprime : PrimrecPred (fun p : ℕ × ℕ => p.1.Coprime p.2) := by
  simpa only [Nat.Coprime] using
    (Primrec.eq.comp primrec_nat_gcd (Primrec.const 1))

lemma rat_encoding (q : ℚ) : encode q = encode (q.num, q.den) := rfl

lemma rat_roundtrip (n : ℕ) : encode (decode (α := ℚ) n) =
    encode ((decode (α := ℤ × ℕ) n).bind fun p =>
      if 0 < p.2 ∧ p.1.natAbs.Coprime p.2 then some (encode p) else none) := by
  simp only [Encodable.decode_ofEquiv, Encodable.decode_sigma_val,
    Encodable.decode_nat, Option.map_some, Option.bind_some, Option.map_map]
  simp only [Encodable.decode, Encodable.decodeSubtype, Option.bind_some]
  dsimp only [Equiv.symm_symm, Equiv.sigmaEquivProd, Equiv.coe_fn_mk, Function.comp_def]
  split_ifs with h <;>
    simp_all [Encodable.encode_ofEquiv, Encodable.Subtype.encode_eq, Nat.Coprime]
  split_ifs with hh
  · exact False.elim (h hh.1 hh.2)
  · rfl

instance ratPrimcodable : Primcodable ℚ :=
  { toEncodable := Rat.instEncodable
    prim := by
      have hg : Primrec (fun p : ℤ × ℕ =>
          if 0 < p.2 ∧ p.1.natAbs.Coprime p.2 then some (encode p) else none) := by
        fun_prop
      have hb : Primrec (fun n : ℕ => (decode (α := ℤ × ℕ) n).bind fun p =>
          if 0 < p.2 ∧ p.1.natAbs.Coprime p.2 then some (encode p) else none) :=
        Primrec.option_bind Primrec.decode (hg.comp Primrec.snd).to₂
      exact (Primrec.nat_iff.mp (Primrec.encode.comp hb)).of_eq (fun n => (rat_roundtrip n).symm) }

@[fun_prop] lemma primrec_rat_num : Primrec Rat.num := by
  have hp : Primrec (fun q : ℚ => (decode (α := ℤ × ℕ) (encode q)).getD (0, 0)) :=
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.encode) (Primrec.const (0, 0)))
  exact (Primrec.fst.comp hp).of_eq fun q => by rw [rat_encoding, Encodable.encodek]; rfl

@[fun_prop] lemma primrec_rat_den : Primrec Rat.den := by
  have hp : Primrec (fun q : ℚ => (decode (α := ℤ × ℕ) (encode q)).getD (0, 0)) :=
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.encode) (Primrec.const (0, 0)))
  exact (Primrec.snd.comp hp).of_eq fun q => by rw [rat_encoding, Encodable.encodek]; rfl

end RapidForcing.EffectiveArithmetic

end

end OAI
