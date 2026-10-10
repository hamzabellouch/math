import OAI.Probability.SignedSweeps.UniquePaths

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def finiteProb {A : Type*} [Fintype A] (P : A → Prop) : ℝ :=
  finiteMean ℝ (fun a => if P a then 1 else 0)

lemma finiteProb_congr {A : Type*} [Fintype A] {P Q : A → Prop}
    (h : ∀ a, P a ↔ Q a) : finiteProb P = finiteProb Q := by
  unfold finiteProb
  apply finiteMean_congr
  intro a
  simp only [h a]

lemma finiteProb_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B)
    (P : B → Prop) : finiteProb (fun a => P (e a)) = finiteProb P := by
  unfold finiteProb
  exact finiteMean_equiv ℝ e (fun b => if P b then 1 else 0)

@[simp] lemma finiteProb_true (A : Type*) [Fintype A] [Nonempty A] :
    finiteProb (fun _ : A => True) = 1 := by
  simp only [finiteProb, ↓reduceIte]
  exact finiteMean_const ℝ 1

@[simp] lemma finiteProb_false (A : Type*) [Fintype A] :
    finiteProb (fun _ : A => False) = 0 := by
  simp [finiteProb, finiteMean]

lemma finiteProb_nonneg {A : Type*} [Fintype A] (P : A → Prop) : 0 ≤ finiteProb P := by
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_nonneg (fun a _ => by split_ifs <;> norm_num)

lemma finiteProb_mono {A : Type*} [Fintype A] {P Q : A → Prop}
    (h : ∀ a, P a → Q a) : finiteProb P ≤ finiteProb Q := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : P a
  · simp only [ite_eq_left hp, ite_eq_left (h a hp), le_refl]
  · simp only [ite_eq_right hp]
    split_ifs <;> norm_num

lemma finiteProb_le_one {A : Type*} [Fintype A] [Nonempty A] (P : A → Prop) :
    finiteProb P ≤ 1 := by
  simpa using finiteProb_mono (Q := fun _ : A => True) (fun _ _ => True.intro)

lemma finiteProb_pi_forall {I : Type*} [Fintype I] [DecidableEq I] (A : I → Type*) [∀ i, Fintype (A i)]
    (P : ∀ i, A i → Prop) :
    finiteProb (fun a : ∀ i, A i => ∀ i, P i (a i)) = ∏ i, finiteProb (P i) := by
  simp only [finiteProb, finiteMean, smul_eq_mul, Fintype.card_pi, Nat.cast_prod]
  rw [Finset.prod_mul_distrib, Fintype.prod_sum, ← Finset.prod_inv_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : ∀ i, P i (a i)
  · simp [h]
  · rw [ite_eq_right h]
    symm
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma univ_perms_fin_two : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
    {1, Equiv.swap 0 1} := by
  symm
  apply Finset.eq_univ_of_card
  have hs : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
    intro h
    have hz := congrArg (fun p : Equiv.Perm (Fin 2) => p 0) h
    norm_num at hz
  simp [hs, Fintype.card_perm]

lemma finiteProb_bit_switch (a b : Fin 2) :
    finiteProb (fun p : Equiv.Perm (Fin 2) => p a = b) = 1 / 2 := by
  unfold finiteProb finiteMean
  rw [univ_perms_fin_two]
  have hs : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
    intro h
    have hz := congrArg (fun p : Equiv.Perm (Fin 2) => p 0) h
    norm_num at hz
  fin_cases a <;> fin_cases b <;> norm_num [hs, Fintype.card_perm]

lemma finiteMean_pi_prod {I : Type*} [Fintype I] [DecidableEq I] (A : I → Type*) [∀ i, Fintype (A i)]
    (f : ∀ i, A i → ℝ) :
    finiteMean ℝ (fun a : ∀ i, A i => ∏ i, f i (a i)) = ∏ i, finiteMean ℝ (f i) := by
  simp only [finiteMean, smul_eq_mul, Fintype.card_pi, Nat.cast_prod]
  rw [Finset.prod_mul_distrib, Fintype.prod_sum, ← Finset.prod_inv_distrib]

end SignedSweeps
end

end OAI
