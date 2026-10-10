import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace OAI

/-! # Permutations and sign counts of distinct positive weight rays -/

noncomputable section

namespace PolycyclicRecognition

variable {W I : Type*} [AddCommGroup W] [Module ℝ W] [Fintype I]

/-- Pullback preserving a finite family of distinct positive rays acts by a
permutation. Distinctness is on rays, not on a possibly repeated generator list. -/
theorem exists_weight_ray_permutation
    (α : I → W →ₗ[ℝ] ℝ) (A : W ≃ₗ[ℝ] W)
    (hdistinct : ∀ i j (r : ℝ), 0 < r → α i = r • α j → i = j)
    (hmaps : ∀ i, ∃ (j : I) (r : ℝ), 0 < r ∧ (α i).comp A.toLinearMap = r • α j) :
    ∃ σ : I ≃ I, ∃ r : I → ℝ, (∀ i, 0 < r i) ∧
      ∀ i, (α i).comp A.toLinearMap = r i • α (σ i) := by
  classical
  choose j r hr heq using hmaps
  have hj : Function.Injective j := by
    intro i k hik
    apply hdistinct i k (r i / r k) (div_pos (hr i) (hr k))
    ext x
    have hi := LinearMap.congr_fun (heq i) (A.symm x)
    have hk := LinearMap.congr_fun (heq k) (A.symm x)
    change α i (A (A.symm x)) = r i * α (j i) (A.symm x) at hi
    change α k (A (A.symm x)) = r k * α (j k) (A.symm x) at hk
    simp only [A.apply_symm_apply] at hi hk
    change α i x = (r i / r k) * α k x
    rw [hik] at hi
    rw [hi, hk]
    field_simp [(hr k).ne']
  let σ : I ≃ I := Equiv.ofBijective j ⟨hj, Finite.surjective_of_injective hj⟩
  exact ⟨σ, r, hr, heq⟩

/-- A ray permutation preserves the number of positive weights at every
vector. This supplies the fixed-count input of the line-sign argument. -/
theorem positive_weight_count_of_ray_permutation
    (α : I → W →ₗ[ℝ] ℝ) (A : W ≃ₗ[ℝ] W) (σ : I ≃ I) (r : I → ℝ)
    (hr : ∀ i, 0 < r i)
    (heq : ∀ i, (α i).comp A.toLinearMap = r i • α (σ i)) (w : W) :
    (Finset.univ.filter (fun i => 0 < α i (A w))).card =
      (Finset.univ.filter (fun i => 0 < α i w)).card := by
  classical
  apply Finset.card_equiv σ
  intro i
  have hi := LinearMap.congr_fun (heq i) w
  change α i (A w) = r i * α (σ i) w at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hi]
  exact mul_pos_iff_of_pos_left (hr i)

omit [Fintype I] in
/-- Genericity is also preserved by the same positive ray permutation. -/
theorem nonzero_weights_of_ray_permutation
    (α : I → W →ₗ[ℝ] ℝ) (A : W ≃ₗ[ℝ] W) (σ : I ≃ I) (r : I → ℝ)
    (hr : ∀ i, 0 < r i)
    (heq : ∀ i, (α i).comp A.toLinearMap = r i • α (σ i))
    (w : W) (hw : ∀ i, α i w ≠ 0) : ∀ i, α i (A w) ≠ 0 := by
  intro i
  have hi := LinearMap.congr_fun (heq i) w
  change α i (A w) = r i * α (σ i) w at hi
  rw [hi]
  exact mul_ne_zero (hr i).ne' (hw (σ i))

end PolycyclicRecognition

end

end OAI
