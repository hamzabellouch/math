import OAI.Analysis.KadisonKastler.WeightedStripOperator
import OAI.Analysis.KadisonKastler.StripContourAverage

namespace OAI

/-! # Applying the scalar strip formula to bounded operators

Extra resolvent powers make the spectral strip norm continuous up to both
edges. Consequently the scalar contour theorem applies to every ambient
operator, with no algebra normalization premise.
-/

namespace KadisonKastler

open Set MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def weightedStripCoefficient (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (X : H →L[ℂ] H)
    (ξ η : H) (z : ℂ) : ℂ :=
  inner ℂ ξ ((weightedStripOperator (M := M) J Ω (-z) * X *
    weightedStripOperator (M := M) J Ω z) η)

theorem weightedStripCoefficient_differentiableOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (X : H →L[ℂ] H) (ξ η : H) :
    DifferentiableOn ℂ (weightedStripCoefficient (M := M) J Ω X ξ η)
      {z : ℂ | |z.re| < 1} := by
  intro z hz
  have hB := weightedStripOperator_differentiableOn (M := M) J Ω
  have hopen : IsOpen {z : ℂ | |z.re| < 1} :=
    isOpen_lt Complex.continuous_re.abs continuous_const
  have hpos := hB.differentiableAt (hopen.mem_nhds hz)
  have hneg := (hB.differentiableAt (hopen.mem_nhds (by simpa using hz))).comp z
    (differentiableAt_id.neg)
  have hm := (hneg.mul_const X).mul hpos
  exact ((innerSL ℂ ξ).differentiableAt.comp z
    (hm.clm_apply (differentiableAt_const η))).differentiableWithinAt

theorem weightedStripCoefficient_bound (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (X : H →L[ℂ] H) (ξ η : H) {z : ℂ} (hz : |z.re| ≤ 1 / 2) :
    ‖weightedStripCoefficient (M := M) J Ω X ξ η z‖ ≤ ‖ξ‖ * ‖X‖ * ‖η‖ := by
  have hp (w : ℂ) (hw : |w.re| ≤ 1 / 2) (v : H) :
      ‖weightedStripOperator (M := M) J Ω w v‖ ≤ ‖v‖ := by
    calc
      _ ≤ ‖weightedStripOperator (M := M) J Ω w‖ * ‖v‖ :=
        (weightedStripOperator (M := M) J Ω w).le_opNorm v
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right
        (weightedStripOperator_norm_le J Ω hw) (norm_nonneg v)
      _ = ‖v‖ := one_mul _
  apply (norm_inner_le_norm _ _).trans
  change ‖ξ‖ * ‖weightedStripOperator (M := M) J Ω (-z)
    (X (weightedStripOperator (M := M) J Ω z η))‖ ≤ _
  calc
    _ ≤ ‖ξ‖ * ‖X (weightedStripOperator (M := M) J Ω z η)‖ :=
      mul_le_mul_of_nonneg_left (hp (-z) (by simpa using hz) _) (norm_nonneg _)
    _ ≤ ‖ξ‖ * (‖X‖ * ‖weightedStripOperator (M := M) J Ω z η‖) :=
      mul_le_mul_of_nonneg_left (X.le_opNorm _) (norm_nonneg _)
    _ ≤ ‖ξ‖ * (‖X‖ * ‖η‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hp z hz η) (norm_nonneg _))
        (norm_nonneg _)
    _ = _ := by ring

theorem weightedStripCoefficient_average (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (X : H →L[ℂ] H) (ξ η : H) (φ : ℝ) (hφ : |φ| < Real.pi) :
    (∫ t : ℝ, stripAverageKernel Real.pi (φ : ℂ) t *
      (Complex.exp (Complex.I * φ / 2) *
          weightedStripCoefficient (M := M) J Ω X ξ η ((1 / 2 : ℂ) + t * Complex.I) +
        Complex.exp (-(Complex.I * φ / 2)) *
          weightedStripCoefficient (M := M) J Ω X ξ η ((-1 / 2 : ℂ) + t * Complex.I))) =
      weightedStripCoefficient (M := M) J Ω X ξ η 0 := by
  have hd := weightedStripCoefficient_differentiableOn (M := M) J Ω X ξ η
  have hc := hd.continuousOn.mono (show {z : ℂ | |z.re| ≤ 1 / 2} ⊆
    {z : ℂ | |z.re| < 1} from fun z hz => (show |z.re| < 1 from lt_of_le_of_lt hz (by norm_num)))
  exact centered_strip_average φ hφ _ hc
    (hd.mono (fun z hz => (show |z.re| < 1 from lt_trans hz (by norm_num))))
    (‖ξ‖ * ‖X‖ * ‖η‖) (by positivity)
    (fun z hz => weightedStripCoefficient_bound J Ω X ξ η hz)

end

end KadisonKastler

end OAI
