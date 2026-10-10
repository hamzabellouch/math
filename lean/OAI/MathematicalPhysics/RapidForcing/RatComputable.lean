import OAI.MathematicalPhysics.RapidForcing.RatPrimrec

namespace OAI

section
open Encodable Denumerable
namespace RapidForcing.EffectiveArithmetic

lemma computable_of_graph {A B : Type} [Primcodable A] [Primcodable B]
    (f : A → B) (R : A → B → Prop) [DecidableRel R]
    (hR : PrimrecPred (fun p : A × B => R p.1 p.2))
    (h : ∀ a b, R a b ↔ b = f a) : Computable f := by
  let test : A → ℕ → Option B := fun a n =>
    (decode n).bind fun b => if R a b then some b else none
  have ht : Primrec₂ test :=
    Primrec.option_bind (Primrec.decode.comp Primrec.snd)
      (Primrec.ite (hR.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
        (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂
  apply (Partrec.rfindOpt ht.to_comp).of_eq_tot
  intro a
  have hd : (Nat.rfindOpt (test a)).Dom := Nat.rfindOpt_dom.mpr
    ⟨encode (f a), f a, by simp [test, Encodable.encodek, (h a (f a)).mpr rfl]⟩
  have hm : (Nat.rfindOpt (test a)).get hd ∈ Nat.rfindOpt (test a) := ⟨hd, rfl⟩
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hm
  have he : (Nat.rfindOpt (test a)).get hd = f a := by
    simp only [test, Option.mem_bind_iff] at hn
    obtain ⟨b, _, hb⟩ := hn
    split_ifs at hb with hab
    · obtain rfl := Option.mem_some_iff.mp hb
      exact (h a _).mp hab
    · contradiction
  exact he ▸ hm

@[fun_prop] lemma primrec_rat_le : PrimrecPred (fun p : ℚ × ℚ => p.1 ≤ p.2) := by
  exact (show PrimrecPred (fun p : ℚ × ℚ => p.1.num * (p.2.den : ℤ) ≤
      p.2.num * (p.1.den : ℤ)) by fun_prop).of_eq (fun p => (Rat.le_iff _ _).symm)

@[fun_prop] lemma primrec_rat_lt : PrimrecPred (fun p : ℚ × ℚ => p.1 < p.2) := by
  exact (PrimrecPred.not (primrec_rat_le.comp (Primrec.snd.pair Primrec.fst))).of_eq
    (fun p => not_le)

lemma rat_div_graph (n : ℤ) (d : ℕ) (q : ℚ) (hd : d ≠ 0) :
    q.num * (d : ℤ) = n * (q.den : ℤ) ↔ q = (n : ℚ) / d := by
  have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  conv_rhs => rw [← Rat.num_div_den q, div_eq_div_iff hq hd']
  exact_mod_cast (Iff.rfl : q.num * (d : ℤ) = n * (q.den : ℤ) ↔ _)

@[fun_prop] lemma computable_rat_divNat : Computable (fun p : ℤ × ℕ => (p.1 : ℚ) / p.2) := by
  apply computable_of_graph _ (fun p q =>
      if p.2 = 0 then q = 0 else q.num * (p.2 : ℤ) = p.1 * (q.den : ℤ))
  · have hi : PrimrecPred (fun p : (ℤ × ℕ) × ℚ =>
        (p.1.2 = 0 ∧ p.2 = 0) ∨ (p.1.2 ≠ 0 ∧ p.2.num * (p.1.2 : ℤ) = p.1.1 * (p.2.den : ℤ))) := by fun_prop
    exact hi.of_eq (fun p => by split_ifs <;> simp_all)
  · intro p q
    split_ifs with hd
    · simp [hd]
    · exact rat_div_graph _ _ _ hd

@[fun_prop] lemma computable_rat_castInt : Computable (fun z : ℤ => (z : ℚ)) := by
  simpa using computable_rat_divNat.comp (Computable.id.pair (Computable.const 1))

@[fun_prop] lemma computable_rat_castNat : Computable (fun n : ℕ => (n : ℚ)) := by
  simpa only [Int.cast_natCast] using computable_rat_castInt.comp primrec_int_cast.to_comp

@[fun_prop] lemma computable_rat_add : Computable (fun p : ℚ × ℚ => p.1 + p.2) := by
  have hh : Primrec (fun p : ℚ × ℚ =>
      (p.1.num * (p.2.den : ℤ) + p.2.num * (p.1.den : ℤ), p.1.den * p.2.den)) := by fun_prop
  apply (computable_rat_divNat.comp hh.to_comp).of_eq
  intro p
  dsimp; push_cast
  conv_rhs => rw [← Rat.num_div_den p.1, ← Rat.num_div_den p.2]
  have h1 : (p.1.den : ℚ) ≠ 0 := by exact_mod_cast p.1.den_nz
  have h2 : (p.2.den : ℚ) ≠ 0 := by exact_mod_cast p.2.den_nz
  field_simp

@[fun_prop] lemma computable_rat_mul : Computable (fun p : ℚ × ℚ => p.1 * p.2) := by
  have hh : Primrec (fun p : ℚ × ℚ => (p.1.num * p.2.num, p.1.den * p.2.den)) := by fun_prop
  apply (computable_rat_divNat.comp hh.to_comp).of_eq
  intro p
  dsimp; push_cast
  rw [mul_div_mul_comm, Rat.num_div_den, Rat.num_div_den]

@[fun_prop] lemma computable_rat_neg : Computable (fun q : ℚ => -q) := by
  have hh : Primrec (fun q : ℚ => (-q.num, q.den)) := by fun_prop
  apply (computable_rat_divNat.comp hh.to_comp).of_eq
  intro q
  simp only [Int.cast_neg, neg_div, Rat.num_div_den]

@[fun_prop] lemma computable_rat_sub : Computable (fun p : ℚ × ℚ => p.1 - p.2) := by
  simpa only [sub_eq_add_neg] using (show Computable (fun p : ℚ × ℚ => p.1 + -p.2) by fun_prop)

end RapidForcing.EffectiveArithmetic

end

end OAI
