import OAI.Probability.SLE.Mass.PhysicalDiskMass
import OAI.Probability.SLE.Mass.DilationMass

namespace OAI

/-! Compatibility of the actual inverse restart mass with spatial normalization. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Multipoint

lemma IsCapacityTwoWitness.inverse_mass_dilation
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F)
    (κ : ℝ) (hκ : 0 < κ) (t : ℝ≥0) (a : ℝ≥0) (ha : 0 < a)
    (μ : Measure upperHalfPlane) :
    weightedImageMass (fun z : upperHalfPlane => F t ((z:ℂ)+(U t:ℂ)))
      (fun z : upperHalfPlane => ENNReal.ofReal
        (‖deriv (F t) ((z:ℂ)+(U t:ℂ))‖^dimension κ)) (dilationMass κ a ha μ) =
    weightedImageMass (fun z : upperHalfPlane => F t ((U t:ℂ)+(a:ℂ)*z))
      (fun z : upperHalfPlane => ENNReal.ofReal
        (‖deriv (fun v : ℂ => F t ((U t:ℂ)+(a:ℂ)*v)) z‖^dimension κ)) μ := by
  let J := fun z : upperHalfPlane => F t ((z:ℂ)+(U t:ℂ))
  let w := fun z : upperHalfPlane => ENNReal.ofReal
    (‖deriv (F t) ((z:ℂ)+(U t:ℂ))‖^dimension κ)
  have hshift (z : upperHalfPlane) : (z:ℂ)+(U t:ℂ) ∈ upperHalfPlane := by
    simpa only [upperHalfPlane,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,add_zero]
      using z.property
  have hJ : Measurable J :=
    ((hw.2.2.2.2.1 t).continuousOn.comp_continuous
      (continuous_subtype_val.add continuous_const) hshift).measurable
  have hwM : Measurable w := by
    have hh : w=(fun z : upperHalfPlane => (hw.restartMassWeight t κ hκ z:ℝ≥0∞)) := by
      funext z
      rw [← ENNReal.ofReal_coe_nnreal]
      rfl
    rw [hh]
    exact (hw.restartMassWeight t κ hκ).continuous.measurable.coe_nnreal_ennreal
  change weightedImageMass J w (weightedImageMass (halfPlaneDilation a ha)
    (fun _ : upperHalfPlane => ENNReal.ofReal ((a:ℝ)^dimension κ)) μ)=_
  rw [weightedImageMass_comp J hJ w hwM _ (halfPlaneDilation a ha).continuous.measurable _
    measurable_const]
  have hmap : J ∘ halfPlaneDilation a ha =
      (fun z : upperHalfPlane => F t ((U t:ℂ)+(a:ℂ)*z)) := by
    funext z
    simp only [Function.comp_apply,J,halfPlaneDilation_apply,add_comm]
  rw [hmap]
  congr 1
  funext z
  change ENNReal.ofReal ((a:ℝ)^dimension κ) *
    ENNReal.ofReal (‖deriv (F t) ((a:ℂ)*z+(U t:ℂ))‖^dimension κ)=_
  have haz : (U t:ℂ)+(a:ℂ)*z ∈ upperHalfPlane := by
    change 0 < ((U t:ℂ)+(a:ℂ)*z).im
    simpa only [Complex.add_im,Complex.ofReal_im,zero_add,Complex.mul_im,
      Complex.ofReal_re,zero_mul,add_zero] using mul_pos (show 0<(a:ℝ) from ha) z.property
  have hFd := (hw.2.2.2.2.1 t).differentiableAt (isOpen_upperHalfPlane.mem_nhds haz)
  have had : HasDerivAt (fun v : ℂ => (U t:ℂ)+(a:ℂ)*v) (a:ℂ) (z:ℂ) := by
    convert ((hasDerivAt_id (z:ℂ)).const_mul (a:ℂ)).const_add (U t:ℂ) using 1 <;> simp
  have hdcomp : deriv (fun v : ℂ => F t ((U t:ℂ)+(a:ℂ)*v)) (z:ℂ)=
      deriv (F t) ((U t:ℂ)+(a:ℂ)*z)*(a:ℂ) := (hFd.hasDerivAt.comp (z:ℂ) had).deriv
  rw [hdcomp,norm_mul,Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
    ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _),Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (show 0<(a:ℝ) from ha),add_comm ((a:ℂ)*z) (U t:ℂ)]
  exact mul_comm _ _

end SLEExactGauge

end

end OAI
