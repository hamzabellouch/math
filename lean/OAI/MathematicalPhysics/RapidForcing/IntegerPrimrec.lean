import OAI.MathematicalPhysics.RapidForcing.Model

namespace OAI

section

open Encodable Denumerable
namespace RapidForcing
namespace EffectiveArithmetic

lemma encode_int_ofNat (n : ℕ) : Encodable.encode (Int.ofNat n) = 2 * n := by
  simp [encode, Equiv.intEquivNat, Equiv.intEquivNatSumNat,
    Equiv.natSumNatEquivNat]
  change Nat.bit false n = _
  simp [Nat.bit_val]

lemma encode_int_negSucc (n : ℕ) : Encodable.encode (Int.negSucc n) = 2 * n + 1 := by
  simp [encode, Equiv.intEquivNat, Equiv.intEquivNatSumNat,
    Equiv.natSumNatEquivNat]

lemma ofNat_int (n : ℕ) : Denumerable.ofNat ℤ n =
    if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2) := by
  apply Encodable.encode_injective
  rw [encode_ofNat]
  split_ifs with hn
  · rw [encode_int_ofNat]
    omega
  · rw [encode_int_negSucc]
    omega

lemma primrec_int_ofNat : Primrec Int.ofNat :=
  Primrec.encode_iff.mp ((Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).of_eq
    (fun n => (encode_int_ofNat n).symm))

lemma primrec_int_negSucc : Primrec Int.negSucc :=
  Primrec.encode_iff.mp ((Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1)).of_eq
      (fun n => (encode_int_negSucc n).symm))

lemma primrec_int_cases {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → ℤ} (hf : Primrec f) {p q : A → ℕ → B}
    (hp : Primrec₂ p) (hq : Primrec₂ q) :
    Primrec (fun a => Int.rec (motive := fun _ => B) (p a) (q a) (f a)) := by
  have he := Primrec.encode.comp hf
  have hd := Primrec.nat_div.comp he (Primrec.const 2)
  have hb := Primrec.nat_mod.comp he (Primrec.const 2)
  have h := Primrec.ite (Primrec.eq.comp hb (Primrec.const 0))
    (hp.comp Primrec.id hd) (hq.comp Primrec.id hd)
  apply h.of_eq
  intro a
  have hh := ofNat_int (Encodable.encode (f a))
  rw [ofNat_encode] at hh
  conv_rhs => rw [hh]
  split_ifs <;> rfl

lemma primrec_int_natAbs : Primrec Int.natAbs := by
  have h := primrec_int_cases Primrec.id Primrec₂.right (Primrec.succ.comp Primrec.snd).to₂
  exact h.of_eq (fun z => by cases z <;> rfl)

lemma primrec_int_toNat : Primrec Int.toNat := by
  have h := primrec_int_cases Primrec.id Primrec₂.right (Primrec₂.const 0)
  exact h.of_eq (fun z => by cases z <;> rfl)

lemma primrec_int_neg : Primrec (fun z : ℤ => -z) := by
  have hn : Primrec (fun n : ℕ => -(n : ℤ)) :=
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 0)
      (primrec_int_negSucc.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))).of_eq
        (fun n => by cases n <;> simp [Int.negSucc_eq])
  have h := primrec_int_cases Primrec.id (hn.comp Primrec.snd).to₂
    (primrec_int_ofNat.comp (Primrec.succ.comp Primrec.snd)).to₂
  exact h.of_eq (fun z => by cases z <;> rfl)

end EffectiveArithmetic
end RapidForcing

end

end OAI
