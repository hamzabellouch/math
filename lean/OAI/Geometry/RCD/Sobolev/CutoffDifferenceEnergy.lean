import OAI.Geometry.RCD.Harmonic.UnboundedCaccioppoli
import OAI.Geometry.RCD.Sobolev.GammaL2Bound
import OAI.Geometry.RCD.Sobolev.ConstantLaplacianBochnerInput

namespace OAI

/-! # Exact cutoff energy of a Poisson function minus a recovery

The admissible test is the square of the actual Lipschitz cutoff times the
Sobolev difference. Neither Sobolev function needs a global value bound.
-/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem cutoff_difference_energy (w q η : SobolevSpace μ hQ)
    {v : X → ℝ} {L B A : ℝ≥0} (hv : LipschitzWith L v)
    (hs : HasCompactSupport v) (hb : ∀ x, |v x|≤B) (hn : ∀ x, 0≤v x)
    (hrep : SobolevSpace.toLp μ hQ η=ᵐ[μ] v)
    (hgrad : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ η x≤A)
    {Ω : Set X} (hsupp : tsupport v⊆Ω) {a : ℝ}
    (hw : IsConstantLaplacianOn μ hQ Ω w a) :
    (∫ x, (v x)^2*localGamma μ hQ (w-q) (w-q) x ∂μ)=
      (∫ x, (v x)^2*localGamma μ hQ q q x ∂μ)-
      (∫ x, (v x)^2*localGamma μ hQ w w x ∂μ)-
      2*a*(∫ x in Ω, (v x)^2*SobolevSpace.toLp μ hQ (w-q) x ∂μ)-
      4*∫ x, v x*SobolevSpace.toLp μ hQ (w-q) x*localGamma μ hQ w η x ∂μ := by
  let z := w-q
  let M := SobolevSpace.cutoffCLM μ hQ hv hs hb hn
  have hvnorm : ∀ᵐ x ∂μ, ‖v x‖≤(B:ℝ) :=
    Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x
  have hv2norm : ∀ᵐ x ∂μ, ‖(v x)^2‖≤(B:ℝ)^2 :=
    Eventually.of_forall fun x => by
      simpa only [norm_pow,Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb x) 2
  have hwi (f g : SobolevSpace μ hQ) : Integrable (fun x => (v x)^2*localGamma μ hQ f g x) μ :=
    (localGamma_memL1 μ hQ f g).bdd_mul (hv.continuous.aestronglyMeasurable.pow 2) hv2norm
  have hΓ : MemLp (localGamma μ hQ w η) 2 μ :=
    (memLp_congr_ae (localGamma_comm μ hQ η w)).mp
      (localGamma_memLp_of_bounded_gradient μ hQ η w A hgrad)
  have hcross : Integrable (fun x => v x*SobolevSpace.toLp μ hQ z x*localGamma μ hQ w η x) μ := by
    convert ((Lp.memLp (SobolevSpace.toLp μ hQ z)).integrable_mul hΓ).bdd_mul
      hv.continuous.aestronglyMeasurable hvnorm using 1
    funext x
    simp only [Pi.mul_apply]
    ring
  have htpoint : localGamma μ hQ w (M (M z))=ᵐ[μ] fun x =>
      (v x)^2*localGamma μ hQ w z x+
        2*(v x*SobolevSpace.toLp μ hQ z x*localGamma μ hQ w η x) := by
    filter_upwards [localGamma_cutoffCLM_right μ hQ (M z) η w hv hs hb hn hrep,
      localGamma_cutoffCLM_right μ hQ z η w hv hs hb hn hrep,
      SobolevSpace.cutoffCLM_coe μ hQ hv hs hb hn z] with x h1 h2 h3
    change localGamma μ hQ w (M (M z)) x=_ at h1
    change localGamma μ hQ w (M z) x=_ at h2
    change SobolevSpace.toLp μ hQ (M z) x=_ at h3
    rw [h1,h2,h3]
    ring
  have htest : energyForm μ hQ w (M (M z))=
      (∫ x, (v x)^2*localGamma μ hQ w z x ∂μ)+
        2*∫ x, v x*SobolevSpace.toLp μ hQ z x*localGamma μ hQ w η x ∂μ := by
    rw [← integral_localGamma_eq_energyForm,integral_congr_ae htpoint,
      integral_add (hwi w z) (hcross.const_mul 2),integral_const_mul]
  have hsource := hw (M (M z)) (SobolevSpace.cutoffCLM_mem_dirichlet μ hQ hv hs hb hn hsupp (M z))
  have htval : SobolevSpace.toLp μ hQ (M (M z))=ᵐ[μ] fun x =>
      (v x)^2*SobolevSpace.toLp μ hQ z x := by
    filter_upwards [SobolevSpace.cutoffCLM_coe μ hQ hv hs hb hn (M z),
      SobolevSpace.cutoffCLM_coe μ hQ hv hs hb hn z] with x h1 h2
    change SobolevSpace.toLp μ hQ (M (M z)) x=_ at h1
    change SobolevSpace.toLp μ hQ (M z) x=_ at h2
    rw [h1,h2]
    ring
  rw [integral_congr_ae (ae_restrict_of_ae htval)] at hsource
  have hpoint : (fun x => (v x)^2*localGamma μ hQ z z x)=ᵐ[μ]
      fun x => (v x)^2*localGamma μ hQ q q x-(v x)^2*localGamma μ hQ w w x+
        2*((v x)^2*localGamma μ hQ w z x) := by
    filter_upwards [localGamma_sub_left μ hQ w q z,
      localGamma_sub_left μ hQ w q w,localGamma_sub_left μ hQ w q q,
      localGamma_comm μ hQ q z,localGamma_comm μ hQ z w,localGamma_comm μ hQ w q]
      with x hz hzw hzq hqz hwz hwq
    change localGamma μ hQ z z x=_ at hz
    change localGamma μ hQ z w x=_ at hzw
    change localGamma μ hQ z q x=_ at hzq
    rw [hz,hqz,hzq,← hwz,hzw,hwq]
    ring
  have he : (∫ x, (v x)^2*localGamma μ hQ z z x ∂μ)=
      (∫ x, (v x)^2*localGamma μ hQ q q x ∂μ)-
      (∫ x, (v x)^2*localGamma μ hQ w w x ∂μ)+
      2*∫ x, (v x)^2*localGamma μ hQ w z x ∂μ := by
    rw [integral_congr_ae hpoint]
    have hadd := integral_add ((hwi q q).sub (hwi w w)) ((hwi w z).const_mul 2)
    simp only [Pi.sub_apply] at hadd
    rw [hadd,integral_sub (hwi q q) (hwi w w),integral_const_mul]
  change (∫ x, (v x)^2*localGamma μ hQ z z x ∂μ)=_
  linarith

end RegularPointCoordinates

end

end OAI
