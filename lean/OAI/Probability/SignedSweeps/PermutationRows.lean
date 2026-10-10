import OAI.Probability.SignedSweeps.FiniteProbability

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma finiteProb_real_kernel_apply {A X : Type*} [Fintype A] [Fintype X]
    (s : A → X) (f : X → ℝ) :
    (∑ y, finiteProb (fun a => s a = y) * f y) = finiteMean ℝ (fun a => f (s a)) := by
  simp only [finiteProb, finiteMean, smul_eq_mul, mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

lemma finiteMean_comm {A B : Type*} [Fintype A] [Fintype B] (f : A → B → ℝ) :
    finiteMean ℝ (fun a => finiteMean ℝ (fun b => f a b)) =
      finiteMean ℝ (fun b => finiteMean ℝ (fun a => f a b)) := by
  simp only [finiteMean, smul_eq_mul, ← Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  ring

lemma finiteMean_mono {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    finiteMean ℝ f ≤ finiteMean ℝ g := by
  apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => h a))
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A X : Type*} [Fintype A] [Fintype X]

def maskedPermutationKernel (f : A → Equiv.Perm X) (R : X → X → Prop) (x y : X) : ℝ :=
  if R x y then finiteProb (fun a => f a x = y) else 0

omit [Fintype X] in
lemma maskedPermutationKernel_nonneg [Fintype X] (f : A → Equiv.Perm X) (R : X → X → Prop) (x y : X) :
    0 ≤ maskedPermutationKernel f R x y := by
  unfold maskedPermutationKernel
  split_ifs
  · exact finiteProb_nonneg _
  · exact le_rfl

omit [Fintype X] in
lemma maskedPermutationKernel_le [Fintype X] (f : A → Equiv.Perm X) (R : X → X → Prop) (x y : X) :
    maskedPermutationKernel f R x y ≤ finiteProb (fun a => f a x = y) := by
  unfold maskedPermutationKernel
  split_ifs
  · exact le_rfl
  · exact finiteProb_nonneg _

lemma maskedPermutationKernel_transpose_sum (f : A → Equiv.Perm X) (R : X → X → Prop) (y : X) :
    (∑ z, maskedPermutationKernel f R z y) =
      finiteProb (fun a => R ((f a).symm y) y) := by
  have he (z : X) : finiteProb (fun a => f a z = y) =
      finiteProb (fun a => (f a).symm y = z) := by
    apply finiteProb_congr
    intro a
    exact ⟨fun h => by rw [← h, Equiv.symm_apply_apply], fun h => by rw [← h, Equiv.apply_symm_apply]⟩
  have hz (z : X) : maskedPermutationKernel f R z y =
      finiteProb (fun a => (f a).symm y = z) * (if R z y then 1 else 0) := by
    unfold maskedPermutationKernel
    rw [he]
    split_ifs <;> ring
  simp only [hz]
  exact finiteProb_real_kernel_apply (fun a => (f a).symm y) (fun z => if R z y then 1 else 0)

theorem maskedPermutationKernel_square_row_le
    (f : A → Equiv.Perm X) (R : X → X → Prop) (x : X) :
    (∑ z, ∑ y, maskedPermutationKernel f R x y * maskedPermutationKernel f R z y) ≤
      finiteMean ℝ (fun b => finiteProb (fun a => R ((f b).symm (f a x)) (f a x))) := by
  calc
    _ ≤ ∑ z, ∑ y, finiteProb (fun a => f a x = y) * maskedPermutationKernel f R z y := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_right (maskedPermutationKernel_le f R x y)
        (maskedPermutationKernel_nonneg f R z y)
    _ = ∑ y, finiteProb (fun a => f a x = y) * finiteProb (fun b => R ((f b).symm y) y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.mul_sum, maskedPermutationKernel_transpose_sum]
    _ = finiteMean ℝ (fun a => finiteProb (fun b => R ((f b).symm (f a x)) (f a x))) :=
      finiteProb_real_kernel_apply _ _
    _ = _ := finiteMean_comm _

lemma nonnegative_kernel_restricted_row_le {Y : Type*} [Fintype Y]
    (e : Y ↪ X) (K : X → X → ℝ) (hK : ∀ x y, 0 ≤ K x y) (x : Y) :
    (∑ z : Y, ∑ y : Y, K (e x) (e y) * K (e z) (e y)) ≤
      ∑ z : X, ∑ y : X, K (e x) y * K z y := by
  apply finite_sum_le_of_injective e e.injective
  · intro z
    apply finite_sum_le_of_injective e e.injective
    · intro y
      exact le_rfl
    · intro y
      exact mul_nonneg (hK _ _) (hK _ _)
  · intro z
    exact Finset.sum_nonneg (fun y _ => mul_nonneg (hK _ _) (hK _ _))

end SignedSweeps
end

end OAI
