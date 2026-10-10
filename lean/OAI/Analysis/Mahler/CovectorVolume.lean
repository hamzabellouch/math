import OAI.Analysis.Mahler.WedgeAlgebra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace OAI

open scoped TensorProduct BigOperators

namespace Mahler
variable {T : Type*} [AddCommGroup T] [Module ℝ T]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The alternating product of a family of real-linear complex covectors. -/
noncomputable def covectorVolume (l : ι → T →ₗ[ℝ] ℂ) : T [⋀^ι]→ₗ[ℝ] ℂ :=
  ((MultilinearMap.mkPiAlgebra ℝ ι ℂ).compLinearMap l).alternatization

lemma covectorVolume_apply (l : ι → T →ₗ[ℝ] ℂ) (v : ι → T) :
    covectorVolume l v = Matrix.det (Matrix.of (fun row column => l column (v row))) := by
  simp only [covectorVolume, MultilinearMap.alternatization_def, Matrix.det_apply,
    Matrix.of_apply, _root_.sum_apply, _root_.smul_apply,
    MultilinearMap.domDomCongr_apply, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply]

/-- Exterior multiplication of simple forms concatenates their covectors,
with the exact shuffle normalization and slot order. -/
theorem wedge_covectorVolume (l : ι → T →ₗ[ℝ] ℂ) (r : κ → T →ₗ[ℝ] ℂ) :
    wedge (covectorVolume l) (covectorVolume r) = covectorVolume (Sum.elim l r) := by
  unfold covectorVolume wedge
  rw [← MultilinearMap.domCoprod_alternization,
    ← LinearMap.compMultilinearMap_alternatization]
  congr 1
  ext v
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.domCoprod_apply,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    LinearMap.mul'_apply, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]

lemma wedge_sum_left {J : Type*} (s : Finset J) (a : J → T [⋀^ι]→ₗ[ℝ] ℂ)
    (b : T [⋀^κ]→ₗ[ℝ] ℂ) : wedge (∑ j ∈ s, a j) b = ∑ j ∈ s, wedge (a j) b := by
  simp only [wedge, ← AlternatingMap.domCoprod'_apply,
    ← LinearMap.compAlternatingMapₗ_apply ℝ, TensorProduct.sum_tmul, map_sum]

lemma wedge_sum_right {J : Type*} (s : Finset J) (a : T [⋀^ι]→ₗ[ℝ] ℂ)
    (b : J → T [⋀^κ]→ₗ[ℝ] ℂ) : wedge a (∑ j ∈ s, b j) = ∑ j ∈ s, wedge a (b j) := by
  simp only [wedge, ← AlternatingMap.domCoprod'_apply,
    ← LinearMap.compAlternatingMapₗ_apply ℝ, TensorProduct.tmul_sum, map_sum]

/-- A change of covectors multiplies the associated volume by its determinant. -/
theorem covectorVolume_linearCombination (C : Matrix ι ι ℂ) (l : ι → T →ₗ[ℝ] ℂ) :
    covectorVolume (fun j => ∑ k, C j k • l k) = C.det • covectorVolume l := by
  ext v
  rw [covectorVolume_apply]
  change Matrix.det (fun i j => (∑ k, C j k • l k) (v i)) = C.det * covectorVolume l v
  rw [covectorVolume_apply]
  let M : Matrix ι ι ℂ := fun i j => l j (v i)
  have hm : ((fun i j => (∑ k, C j k • l k) (v i)) : Matrix ι ι ℂ) =
      M * C.transpose := by
    ext i j
    change (∑ k, C j k • l k) (v i) = ∑ index, l index (v i) * C j index
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hm, Matrix.det_mul, Matrix.det_transpose, mul_comm]
  rfl

lemma covectorVolume_reindex_apply (l : ι → T →ₗ[ℝ] ℂ) (e : κ ≃ ι) (v : κ → T) :
    covectorVolume (l ∘ e) v = covectorVolume l (v ∘ e.symm) := by
  rw [covectorVolume_apply, covectorVolume_apply]
  convert (Matrix.det_submatrix_equiv_self e (fun i j => l j (v (e.symm i)))) using 1 <;>
    first | rfl | (congr 1; ext i j; change _ = l (e j) (v (e.symm (e i))); simp)

end Mahler

end OAI
