import OAI.Probability.SLE.Angle.AngleEigenMoment
import OAI.Probability.SLE.Angle.AngleMomentUniqueness
import OAI.Probability.SLE.Angle.AngleSpectralLaw

namespace OAI

/-! Identification of the actual finite centered angle law with the
explicit positive spectral kernel at every sufficiently large radius time. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Polynomial
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
  (hB : IsBrownianReal B P) (hBm : Measurable (Function.uncurry B))
  (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
  (hκ : 0<κ) (hκ8 : κ<8)
  (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))

include hB hBm hc h0 hκ hκ8 γ G F hw

lemma actual_angle_law_eq_spectral (z : ℂ) (hz : z∈upperHalfPlane)
    (u : ℝ) (hu : angleSpectralMixingTime κ≤u) :
    (finiteCenteredLaw P κ B γ G z u).map
      (extendedMarkedAngle κ B γ G (fun ω => radiusLevelTime (γ ω) (G ω) z u) z)=
        angleSpectralLaw κ u z.arg := by
  have hu0 : 0≤u := (angleSpectralMixingTime_pos hκ).le.trans hu
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.of_uncurry_left
  let S : Ω → WithTop ℝ≥0 := fun ω => radiusLevelTime (γ ω) (G ω) z u
  have hS := actual_radiusLevelTime_stopping hB hm hBm hc h0 κ hκ hκ8 γ G F hw z hz u hu0
  let a := extendedMarkedAngle κ B γ G S z
  have ham : Measurable a :=
    (extendedMarkedAngle_measurable B hm hc κ γ G F hw S hS z).mono hS.measurableSpace_le le_rfl
  let Q := finiteCenteredLaw P κ B γ G z u
  have : IsProbabilityMeasure Q := finiteCenteredLaw_probability hB κ hκ hκ8 γ G F
    (Eventually.of_forall hw) z hz u hu0
  have : IsProbabilityMeasure (angleSpectralLaw κ u z.arg) := angleSpectralLaw_isProbability hκ hu z.arg
  have hang : ∀ᵐ ω ∂Q, a ω∈Ioo (0:ℝ) Real.pi :=
    finiteCenteredLaw_extended_angle_mem hB hc hκ hκ8 γ G F hw z hz u u hu0 le_rfl
  have hfinite : ∀ᵐ ω ∂Q, radiusLevelTime (γ ω) (G ω) z u<∞ := by
    have hh := finiteCenteredLaw_earlier_stop_ae_finite hB hc κ hκ hκ8 γ G F
      (Eventually.of_forall hw) z hz u u hu0 le_rfl S (Eventually.of_forall fun _ => le_rfl)
    exact hh.mono fun ω hω => lt_top_iff_ne_top.mpr hω
  apply angleMeasures_eq_of_eigenMoments κ
  · exact (ae_map_iff ham.aemeasurable measurableSet_Icc).mpr (hang.mono fun _ h => ⟨h.1.le,h.2.le⟩)
  · exact (angleSpectralLaw_ae_mem z.arg).mono fun _ h => ⟨h.1.le,h.2.le⟩
  · intro n
    rw [integral_map ham.aemeasurable
      (anglePolynomialTest_integrable (Q.map a) (angleEigenPolynomial κ n)).aestronglyMeasurable,
      angleSpectralLaw_eigen_moment hκ hu]
    change (∫ ω, (angleEigenPolynomial κ n).eval (Real.cos (a ω)) ∂Q)=_
    calc
      _ = ∫ ω, (angleEigenPolynomial κ n).eval (Real.cos
          ((G ω (radiusLevelTime (γ ω) (G ω) z u).toNNReal z-
            (Real.sqrt κ*B (radiusLevelTime (γ ω) (G ω) z u).toNNReal ω:ℝ)).arg)) ∂Q := by
        apply integral_congr_ae
        filter_upwards [hfinite] with ω hω
        rw [show a ω= _ from extendedMarkedAngle_at_finite_radius κ B hc γ G F hw z u ω hω]
      _ = _ := finiteCenteredLaw_eigen_moment hB hBm hc h0 hκ hκ8 γ G F
        (Eventually.of_forall hw) z hz u hu0 n

end SLEExactGauge

end

end OAI
