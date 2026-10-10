import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.CoordinateMetricFlux

namespace OAI

noncomputable section
open Set Filter Function Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {E F H ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
lemma blockDiagonal_inverse (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hA : IsUnit A.det) (hB : IsUnit B.det) :
    (Matrix.fromBlocks A 0 0 B)⁻¹ = Matrix.fromBlocks A⁻¹ 0 0 B⁻¹ := by
  have h := Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff A (0 : Matrix ι κ ℝ) B
    (iff_of_true ((Matrix.isUnit_iff_isUnit_det A).mpr hA) ((Matrix.isUnit_iff_isUnit_det B).mpr hB))
  simpa using h
omit [FiniteDimensional ℝ E] in
lemma coordinateMetricLaplacian_split (P : H →L[ℝ] E) (Q : H →L[ℝ] F)
    (a : Module.Basis ι ℝ E) (_ : Module.Basis κ ℝ F) (c : Module.Basis (ι ⊕ κ) ℝ H)
    (hPa : ∀ i, P (c (.inl i))=a i) (hPb : ∀ j, P (c (.inr j))=0)
    (hQa : ∀ i, Q (c (.inl i))=0)
    (A : E → Matrix ι ι ℝ) (B : F → Matrix κ κ ℝ)
    (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (hpA : ∀ x, 0 < (A x).det) (hpB : ∀ x, 0 < (B x).det)
    (u : E → ℝ) (hu : ContDiff ℝ ∞ u) (x : H) :
    coordinateMetricLaplacian c (fun y => Matrix.fromBlocks (A (P y)) 0 0 (B (Q y))) (u ∘ P) x =
      coordinateMetricLaplacian a A u (P x) := by
  let ρ : H → ℝ := fun y => Real.sqrt (B (Q y)).det
  have hd (y : H) (v : H) : fderiv ℝ (u ∘ P) y v = fderiv ℝ u (P y) (P v) := by
    rw [fderiv_comp y (hu.differentiable (by simp) _) P.differentiableAt, P.fderiv]
    rfl
  have hρ : Differentiable ℝ ρ := fun y =>
    (((differentiable_det _).comp (Q y) (hB (Q y))).comp y Q.differentiableAt).sqrt (hpB (Q y)).ne'
  have hρa (i : ι) : fderiv ℝ ρ x (c (.inl i))=0 := by
    have hD := ((((differentiable_det _).comp (Q x) (hB (Q x))).sqrt (hpB (Q x)).ne').hasFDerivAt.comp x Q.hasFDerivAt)
    change (fderiv ℝ ((fun y => Real.sqrt ((Matrix.det ∘ B) y)) ∘ Q) x) _ = _
    rw [hD.fderiv]
    simp [ContinuousLinearMap.comp_apply,hQa]
  have hf (y : H) (i : ι) :
      coordinateMetricFlux c (fun z => Matrix.fromBlocks (A (P z)) 0 0 (B (Q z))) (u ∘ P) y (.inl i) =
        ρ y * coordinateMetricFlux a A u (P y) i := by
    simp only [coordinateMetricFlux,Matrix.det_fromBlocks_zero₂₁,
      blockDiagonal_inverse _ _ (isUnit_iff_ne_zero.mpr (hpA (P y)).ne') (isUnit_iff_ne_zero.mpr (hpB (Q y)).ne'),
      Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
      zero_mul,Finset.sum_const_zero,add_zero,hd,hPa]
    rw [Real.sqrt_mul (hpA (P y)).le]
    dsimp [ρ]
    ring
  have hv (j : κ) :
      (fun y => coordinateMetricFlux c (fun z => Matrix.fromBlocks (A (P z)) 0 0 (B (Q z))) (u ∘ P) y (.inr j)) = 0 := by
    funext y
    simp only [coordinateMetricFlux,
      blockDiagonal_inverse _ _ (isUnit_iff_ne_zero.mpr (hpA (P y)).ne') (isUnit_iff_ne_zero.mpr (hpB (Q y)).ne'),
      Fintype.sum_sum_type,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,Pi.zero_apply,
      zero_mul,Finset.sum_const_zero,zero_add,hd,hPb,map_zero,mul_zero]
  have hflux (i : ι) : Differentiable ℝ (fun y => coordinateMetricFlux a A u y i) := fun y =>
    (differentiableAt_pi.mp (differentiableAt_coordinateMetricFlux
      ((hu.of_le (show (2:WithTop ℕ∞) ≤ ∞ from ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt) (hA y) (hpA y) a) i)
  have ha (i : ι) : fderiv ℝ (fun y => coordinateMetricFlux c
      (fun z => Matrix.fromBlocks (A (P z)) 0 0 (B (Q z))) (u ∘ P) y (.inl i)) x (c (.inl i)) =
      ρ x * fderiv ℝ (fun y => coordinateMetricFlux a A u y i) (P x) (a i) := by
    simp_rw [hf]
    change fderiv ℝ (ρ * ((fun y => coordinateMetricFlux a A u y i) ∘ P)) x _ = _
    rw [fderiv_mul (hρ x) ((hflux i (P x)).comp x P.differentiableAt)]
    rw [fderiv_comp x (hflux i (P x)) P.differentiableAt,P.fderiv]
    simp [ContinuousLinearMap.comp_apply,hρa,hPa]
  simp only [coordinateMetricLaplacian,Matrix.det_fromBlocks_zero₂₁,Fintype.sum_sum_type]
  simp_rw [ha,hv]
  simp only [fderiv_zero]
  rw [← Finset.mul_sum,Real.sqrt_mul (hpA (P x)).le]
  dsimp [ρ]
  have hn := (Real.sqrt_pos.mpr (hpB (Q x))).ne'
  field_simp
  simp
end YauCounterexamples
end

end OAI
