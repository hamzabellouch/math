import OAI.Analysis.NumericalRange.OrderedDensities

namespace OAI

universe u_257

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {n m : ℕ} [Nonempty (Fin n)]
lemma cauchy_adjoint (m : Type u_257) [Fintype m] [DecidableEq m] :
    (D.cauchy (m := m)).adjoint = matrixFourier.cauchyAdjoint D.kernel.matrixM :=
  matrixFourier.adjoint_cauchy D.kernel.matrixM D.kernel.matrixM_swap

theorem extremal_condition_bound (A : Matrix (Fin n) (Fin n) ℂ)
    (hW : numericalRange A ⊆ D.domain)
    {S : Matrix (Fin n) (Fin n) ℂ} (hS : S.IsHermitian) (hu : IsUnit S)
    (hc : (matrixAnalyticEval (S*A*S⁻¹) D.interior.toDisk)ᴴ *
      matrixAnalyticEval (S*A*S⁻¹) D.interior.toDisk ≤ 1)
    {κ : ℝ} (hκ : 0 < κ) {X Y : Matrix (Fin n) (Fin m) ℂ}
    (hX : S*X = (κ:ℂ) • X) (hY : S*Y = Y)
    (hx : ‖vectorize X‖ = 1) (hy : ‖vectorize Y‖ = 1) (hXY : Xᴴ*Y = 0)
    {F : ℂ → Matrix (Fin m) (Fin m) ℂ} (hF : AnalyticOnNhd ℂ F (closure D.domain))
    (hn : ∀ z ∈ closure D.domain, ‖F z‖ ≤ 1)
    (he : Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ)
      (completeAnalyticEval (S*A*S⁻¹) F) (vectorize X) = vectorize Y) : κ ≤ 2 := by
  have hA : spectrum ℂ A ⊆ D.domain := (spectrum_subset_numericalRange A).trans hW
  have hA' : spectrum ℂ (S*A*S⁻¹) ⊆ D.domain := by rwa [spectrum_matrix_similarity hu]
  let Λ := D.positiveDensity (S*A*S⁻¹) hA'
  have hΛ : ∀ t, (Λ t).IsHermitian := fun t =>
    (Matrix.nonneg_iff_posSemidef.mp (D.positiveDensity_nonneg (S*A*S⁻¹) hA' hc t)).isHermitian
  have hrep (v : ℂ → Matrix (Fin m) (Fin m) ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
      completeAnalyticEval (S*A*S⁻¹) v = ∫ t, Λ t ⊗ₖ D.trace v hv t ∂AddCircle.haarAddCircle :=
    D.positiveDensity_representation (S*A*S⁻¹) hA' hv
  let p := densityField (μ := AddCircle.haarAddCircle) Λ X X
  let q := densityField (μ := AddCircle.haarAddCircle) Λ Y Y
  let r := densityField (μ := AddCircle.haarAddCircle) Λ X Y
  have hpJ : l2Star p = p := densityField_star Λ hΛ X X
  have hqJ : l2Star q = q := densityField_star Λ hΛ Y Y
  obtain ⟨L,R,hLn,hRn,hLa,hRa,hLC,hRC⟩ := D.ordered_modules hF hn
  have hord := D.positive_ordered (S*A*S⁻¹) hA' hc hF hn hx hy he
  obtain ⟨hp,hq⟩ := densityField_ordered_adjoints Λ (D.trace F hF) X Y L R hLa hRa hord
  have hm := actual_density_means (μ := AddCircle.haarAddCircle) Λ
    (D.positiveDensity_mass (S*A*S⁻¹) hA') hx hXY
  have hr0 : matrixFourier.proj 0 r = 0 := densityField_mean_zero Λ X Y hm.1
  have hp0 : matrixFourier.proj 0 p ≠ 0 := densityField_mean_nonzero Λ X hm.2
  let E := hermitianField (⟨D.resolventField A,D.resolvent_continuous A hA⟩ : C(UnitAddCircle,Matrix (Fin n) (Fin n) ℂ))
  have hE : ∀ t, (E t).PosSemidef := D.resolventField_posSemidef A hW
  have hXid : densityField (μ := AddCircle.haarAddCircle) E X X =
      D.cauchy.adjoint p + l2Star (D.cauchy.adjoint p) := by
    have hh := D.resolvent_density_identification A hA hS hu Λ hΛ hrep hκ.ne' hκ.ne' hX hX
    simpa only [div_self hκ.ne',Complex.ofReal_one,one_smul,show l2Star (densityField (μ := AddCircle.haarAddCircle) Λ X X) = p from hpJ] using hh
  have hY' : S*Y = ((1:ℝ):ℂ) • Y := by
    simpa only [Complex.ofReal_one,one_smul] using hY
  have hYid : densityField (μ := AddCircle.haarAddCircle) E Y Y =
      D.cauchy.adjoint q + l2Star (D.cauchy.adjoint q) := by
    have hh := D.resolvent_density_identification A hA hS hu Λ hΛ hrep one_ne_zero one_ne_zero hY' hY'
    simpa only [div_self one_ne_zero,Complex.ofReal_one,one_smul,show l2Star (densityField (μ := AddCircle.haarAddCircle) Λ Y Y) = q from hqJ] using hh
  have hXYid : densityField (μ := AddCircle.haarAddCircle) E X Y =
      (κ:ℂ) • D.cauchy.adjoint r + ((κ⁻¹:ℝ):ℂ) • l2Star (D.cauchy.adjoint (l2Star r)) := by
    have hh := D.resolvent_density_identification A hA hS hu Λ hΛ hrep hκ.ne' one_ne_zero hX hY'
    simpa only [div_one,one_div] using hh
  have hblock := densityField_block_bound E hE X Y
  rw [hXid,hYid,hXYid,D.cauchy_adjoint (Fin m)] at hblock
  exact matrixFourier.density_comparison_core l2Star matrixFourier_star_zero matrixFourier_star_positive
    D.kernel.matrixM L R D.kernel.matrixM_norm_le hLn hRn D.kernel.matrixM_swap hLC hRC
    p q r hp hq hpJ hqJ hr0 hp0 κ hκ hblock
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
