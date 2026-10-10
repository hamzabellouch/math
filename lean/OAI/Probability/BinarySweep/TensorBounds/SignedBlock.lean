import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungResolution

namespace OAI

noncomputable section

section

open scoped BigOperators Classical Kronecker
open Equiv Matrix

namespace BinaryCoordinateSweeps.Signed
variable {A : Type*} [Fintype A] [DecidableEq A] {n m : ℕ}

@[simp] lemma sumPerm_inv (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin m)) :
    (sumPerm g h)⁻¹ = sumPerm g⁻¹ h⁻¹ := by
  apply Equiv.ext
  intro i
  apply (sumPerm g h).injective
  change (sumPerm g h) ((sumPerm g h).symm i) = _
  rw [Equiv.apply_symm_apply]
  induction i using Fin.addCases with
  | left i => simp
  | right i => simp

lemma signC_sum (β : Fin (n+m) → Bool)
    (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin m)) :
    signC β (sumPerm g h) =
      signC (fun i => β (i.castAdd m)) g * signC (fun i => β (i.natAdd n)) h := by
  simp only [signC,koszulSign_sum,Units.val_mul,Int.cast_mul]

def splitWord : (Fin (n+m) → A) ≃ (Fin n → A) × (Fin m → A) :=
  (finSumFinEquiv.symm.arrowCongr (Equiv.refl A)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

omit [Fintype A] [DecidableEq A] in
@[simp] lemma splitWord_fst (x : Fin (n+m) → A) (i : Fin n) :
    (splitWord x).1 i = x (i.castAdd m) := rfl
omit [Fintype A] [DecidableEq A] in
@[simp] lemma splitWord_snd (x : Fin (n+m) → A) (i : Fin m) :
    (splitWord x).2 i = x (i.natAdd n) := rfl

omit [Fintype A] [DecidableEq A] in
lemma splitWord_comp (x : Fin (n+m) → A) (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin m)) :
    splitWord (x ∘ sumPerm g h) = ((splitWord x).1 ∘ g,(splitWord x).2 ∘ h) := by
  apply Prod.ext <;> funext i <;> simp

lemma actionMatrix_apply (p : A → Bool) (g : Equiv.Perm (Fin n)) (x y : Fin n → A) :
    LinearMap.toMatrix' (act p g) x y = if x ∘ g = y then signC (p ∘ x) g⁻¹ else 0 := by
  simp only [LinearMap.toMatrix'_apply,act_apply,Pi.single_apply]
  split_ifs with h
  · simp
  · simp

theorem actionMatrix_sum (p : A → Bool) (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin m)) :
    LinearMap.toMatrix' (act p (sumPerm g h)) =
      ((LinearMap.toMatrix' (act p g)) ⊗ₖ (LinearMap.toMatrix' (act p h))).submatrix splitWord splitWord := by
  ext x y
  change LinearMap.toMatrix' (act p (sumPerm g h)) x y =
    LinearMap.toMatrix' (act p g) (splitWord x).1 (splitWord y).1 *
      LinearMap.toMatrix' (act p h) (splitWord x).2 (splitWord y).2
  rw [actionMatrix_apply,actionMatrix_apply,actionMatrix_apply,sumPerm_inv,signC_sum]
  have he : x ∘ sumPerm g h = y ↔
      (splitWord x).1 ∘ g = (splitWord y).1 ∧ (splitWord x).2 ∘ h = (splitWord y).2 := by
    rw [← splitWord.injective.eq_iff,splitWord_comp,Prod.mk.injEq]
  simp only [he]
  split_ifs <;> simp_all only [zero_mul,mul_zero,and_self,not_true_eq_false,true_and,false_and]; rfl

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

abbrev actionMatrix (p : A → Bool) (g : Equiv.Perm (Fin n)) := LinearMap.toMatrix' (act p g)

lemma actionMatrix_conjugate_apply (p : A → Bool) (g : Equiv.Perm (Fin n))
    (M : Matrix (Fin n → A) (Fin n → A) ℂ) (x y : Fin n → A) :
    (actionMatrix p g * M * (actionMatrix p g).conjTranspose) x y=
      signC (p ∘ x) g⁻¹ * signC (p ∘ y) g⁻¹ * M (x ∘ g) (y ∘ g) := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,actionMatrix_apply]
  simp [apply_ite,signC_star,mul_assoc,mul_left_comm,mul_comm]

lemma actionMatrix_unitary (p : A → Bool) (g : Equiv.Perm (Fin n)) :
    actionMatrix p g * (actionMatrix p g).conjTranspose=1 := by
  have he (x y : Fin n → A) : x ∘ g = y ∘ g ↔ x=y :=
    (wordReorder g).injective.eq_iff
  ext x y
  have hh := actionMatrix_conjugate_apply p g 1 x y
  rw [mul_one] at hh
  rw [hh]
  by_cases h:x=y
  · subst y
    simp only [Matrix.one_apply,ite_true,signC_sq,mul_one]
  · simp [he,h]

lemma actionMatrix_star_mul (p : A → Bool) (g : Equiv.Perm (Fin n)) :
    (actionMatrix p g).conjTranspose * actionMatrix p g = 1 :=
  mul_eq_one_comm.mp (actionMatrix_unitary p g)

theorem even_tensor_covariance (p : A → Bool) (g : Equiv.Perm (Fin n))
    (M : Fin n → Matrix A A ℂ)
    (hM : ∀ i a b, p a ≠ p b → M i a b=0) :
    actionMatrix p g * tensorMatrices M * (actionMatrix p g).conjTranspose =
      tensorMatrices (fun i => M (g⁻¹ i)) := by
  ext x y
  rw [actionMatrix_conjugate_apply]
  have he : tensorMatrices M (x ∘ g) (y ∘ g) = tensorMatrices (fun i => M (g⁻¹ i)) x y := by
    simpa [tensorMatrices] using
      Equiv.prod_comp g (fun i => M (g⁻¹ i) (x i) (y i))
  rw [he]
  by_cases h : p ∘ x=p ∘ y
  · rw [h,signC_sq,one_mul]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    have hz : tensorMatrices (fun i => M (g⁻¹ i)) x y=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hM _ _ _ hi)
    rw [hz,mul_zero]

end BinaryCoordinateSweeps.Signed

end

end OAI
