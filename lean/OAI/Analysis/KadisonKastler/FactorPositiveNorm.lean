import OAI.Analysis.KadisonKastler.PositiveFactorCorners

namespace OAI

/-! # Additivity of positive norms across a factor and its commutant -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem upperSpectralCut_ne_zero_of_lt_norm
    (y : H →L[ℂ] H) (hy : 0 ≤ y) (t : ℝ) (ht : 0 ≤ t) (hty : t < ‖y‖) :
    upperSpectralCut y t ≠ 0 := by
  intro hz
  have hh := shifted_mul_complement_upperSpectralCut y hy.isSelfAdjoint t
  rw [hz, sub_zero, mul_one] at hh
  have hu : y ≤ t • 1 := sub_nonpos.mp (by
    rw [hh]
    exact neg_nonpos.mpr (CFC.negPart_nonneg _))
  have hn := (CStarAlgebra.norm_le_iff_le_algebraMap y ht hy).mpr
    (by simpa only [Algebra.algebraMap_eq_smul_one] using hu)
  exact (not_le_of_gt hty) hn

theorem norm_add_positive_factor_commutant
    (M : VonNeumannAlgebra H) (hM : ScalarCenter M)
    (x y : H →L[ℂ] H) (hxM : x ∈ M) (hyM : y ∈ M.commutant)
    (hx : 0 ≤ x) (hy : 0 ≤ y) : ‖x + y‖ = ‖x‖ + ‖y‖ := by
  apply le_antisymm (norm_add_le _ _)
  by_contra hn
  have hlt : ‖x + y‖ < ‖x‖ + ‖y‖ := lt_of_not_ge hn
  have hxle : ‖x‖ ≤ ‖x + y‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (le_add_of_nonneg_right hy) hx
  let t := (‖x + y‖ - ‖x‖ + ‖y‖) / 2
  have ht : 0 ≤ t := by dsimp [t]; linarith [norm_nonneg y]
  have hty : t < ‖y‖ := by dsimp [t]; linarith
  let p := upperSpectralCut y t
  have hp : IsStarProjection p := upperSpectralCut_isStarProjection y t
  have hp0 : p ≠ 0 := upperSpectralCut_ne_zero_of_lt_norm y hy t ht hty
  let E := p.range
  let : CompleteSpace E :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range hp.isIdempotentElem).completeSpace_coe
  let : Nontrivial E := nontrivial_projection_range p hp hp0
  have hpe : p = E.starProjection := (isStarProjection_iff_eq_starProjection_range.mp hp).2
  have hE : E.starProjection ∈ M.commutant :=
    hpe ▸ upperSpectralCut_mem M.commutant y hyM t
  have hE0 : E.starProjection ≠ 0 := hpe ▸ hp0
  have hcp : cornerCompression E p = 1 := by
    rw [hpe, ← cornerExtension_one, cornerCompression_extension]
  have hcy : t • (1 : E →L[ℂ] E) ≤ cornerCompression E y := by
    have h := cornerCompression_mono E (smul_upperSpectralCut_le y hy t)
    rw [(cornerCompression E).map_smul_of_tower, hcp] at h
    exact h
  have hbound := norm_add_le_of_compressed_lower E M hM hE hE0 x y hxM hx t ht hcy
  dsimp [t] at hbound
  linarith

end

end KadisonKastler

end OAI
