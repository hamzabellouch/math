import OAI.Geometry.RCD.Harmonic.UnboundedCaccioppoli
import OAI.Geometry.RCD.Sobolev.GammaL2Bound
import OAI.Geometry.RCD.Harmonic.HarmonicGrams

namespace OAI

/-! # Moving a derivative onto a compact Lipschitz test

The unbounded factor needs only its original global Sobolev membership.
-/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem harmonic_nonnegative_cutoff_swap (f w η : SobolevSpace μ hQ)
    {v : X → ℝ} {L B A : ℝ≥0} (hv : LipschitzWith L v)
    (hs : HasCompactSupport v) (hb : ∀ x, |v x|≤B) (hn : ∀ x, 0≤v x)
    (hrep : SobolevSpace.toLp μ hQ η=ᵐ[μ] v)
    (hgrad : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ η x≤A)
    {Ω : Set X} (hsupp : tsupport v⊆Ω) (hw : IsSobolevHarmonicOn μ hQ Ω w) :
    (∫ x, v x*localGamma μ hQ f w x ∂μ)=
      -(∫ x, SobolevSpace.toLp μ hQ f x*localGamma μ hQ η w x ∂μ) := by
  have hi := (localGamma_memL1 μ hQ f w).bdd_mul hv.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hj : Integrable (fun x => SobolevSpace.toLp μ hQ f x*localGamma μ hQ η w x) μ :=
    (Lp.memLp (SobolevSpace.toLp μ hQ f)).integrable_mul
      (localGamma_memLp_of_bounded_gradient μ hQ η w A hgrad)
  have h := hw (SobolevSpace.cutoffCLM μ hQ hv hs hb hn f)
    (SobolevSpace.cutoffCLM_mem_dirichlet μ hQ hv hs hb hn hsupp f)
  rw [energyForm_comm,← integral_localGamma_eq_energyForm,
    integral_congr_ae (localGamma_cutoffCLM μ hQ f η w hv hs hb hn hrep)] at h
  rw [integral_add hi hj] at h
  linarith

variable [IsFiniteMeasureOnCompacts μ]

theorem harmonic_signed_cutoff_swap (f w η : SobolevSpace μ hQ)
    {v : X → ℝ} {L B : ℝ≥0} (hv : LipschitzWith L v)
    (hs : HasCompactSupport v) (hb : ∀ x, |v x|≤B)
    (hrep : SobolevSpace.toLp μ hQ η=ᵐ[μ] v)
    {Ω : Set X} (hsupp : tsupport v⊆Ω) (hw : IsSobolevHarmonicOn μ hQ Ω w) :
    (∫ x, v x*localGamma μ hQ f w x ∂μ)=
      -(∫ x, SobolevSpace.toLp μ hQ f x*localGamma μ hQ η w x ∂μ) := by
  let vp : X → ℝ := fun x => max (v x) 0
  let vm : X → ℝ := fun x => max (-v x) 0
  have hsp : HasCompactSupport vp := hs.comp_left (g := fun t : ℝ => max t 0) (by simp)
  have hsm : HasCompactSupport vm := hs.comp_left (g := fun t : ℝ => max (-t) 0) (by simp)
  have hlp : LipschitzWith L vp := hv.max_const 0
  have hlm : LipschitzWith L vm := hv.neg.max_const 0
  have hbp (x : X) : |vp x|≤B := by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans (hb x)) B.coe_nonneg
  have hbm (x : X) : |vm x|≤B := by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le ((neg_le_abs _).trans (hb x)) B.coe_nonneg
  have hps : tsupport vp⊆Ω := (closure_minimal (by
    intro x hx
    apply subset_tsupport v
    intro hvx
    exact hx (by simp [vp,hvx])) (isClosed_tsupport v)).trans hsupp
  have hms : tsupport vm⊆Ω := (closure_minimal (by
    intro x hx
    apply subset_tsupport v
    intro hvx
    exact hx (by simp [vm,hvx])) (isClosed_tsupport v)).trans hsupp
  let ηp : SobolevSpace μ hQ := SobolevSpace.ofLipschitzCompact μ hQ hlp hsp
  let ηm : SobolevSpace μ hQ := SobolevSpace.ofLipschitzCompact μ hQ hlm hsm
  have hp : SobolevSpace.toLp μ hQ ηp=ᵐ[μ] vp :=
    SobolevSpace.ofLipschitzCompact_coe μ hQ hlp hsp
  have hm : SobolevSpace.toLp μ hQ ηm=ᵐ[μ] vm :=
    SobolevSpace.ofLipschitzCompact_coe μ hQ hlm hsm
  have hvsplit (x : X) : v x=vp x-vm x := by
    dsimp only [vp,vm]
    by_cases hx : 0≤v x
    · rw [max_eq_left hx,max_eq_right (neg_nonpos.mpr hx),sub_zero]
    · have hx' : v x≤0 := (lt_of_not_ge hx).le
      rw [max_eq_right hx',max_eq_left (neg_nonneg.mpr hx')]
      ring
  have he : η=ηp-ηm := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hrep,hp,hm,Lp.coeFn_sub (SobolevSpace.toLp μ hQ ηp)
      (SobolevSpace.toLp μ hQ ηm)] with x hx hpx hmx hsx
    change SobolevSpace.toLp μ hQ η x=SobolevSpace.toLp μ hQ (ηp-ηm) x
    rw [map_sub,hsx,Pi.sub_apply,hx,hpx,hmx]
    exact hvsplit x
  have hpg := SobolevSpace.minimalSlope_le_lipschitz μ hQ ηp hlp hp
  have hmg := SobolevSpace.minimalSlope_le_lipschitz μ hQ ηm hlm hm
  have hpint := harmonic_nonnegative_cutoff_swap μ hQ f w ηp hlp hsp hbp
    (fun _ => le_max_right _ _) hp hpg hps hw
  have hmint := harmonic_nonnegative_cutoff_swap μ hQ f w ηm hlm hsm hbm
    (fun _ => le_max_right _ _) hm hmg hms hw
  have hip := (localGamma_memL1 μ hQ f w).bdd_mul hlp.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbp x)
  have him := (localGamma_memL1 μ hQ f w).bdd_mul hlm.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbm x)
  have hjp : Integrable (fun x => SobolevSpace.toLp μ hQ f x*localGamma μ hQ ηp w x) μ := (Lp.memLp (SobolevSpace.toLp μ hQ f)).integrable_mul
    (localGamma_memLp_of_bounded_gradient μ hQ ηp w L hpg)
  have hjm : Integrable (fun x => SobolevSpace.toLp μ hQ f x*localGamma μ hQ ηm w x) μ := (Lp.memLp (SobolevSpace.toLp μ hQ f)).integrable_mul
    (localGamma_memLp_of_bounded_gradient μ hQ ηm w L hmg)
  have hvint : (∫ x, v x*localGamma μ hQ f w x ∂μ)=
      (∫ x, vp x*localGamma μ hQ f w x ∂μ)-(∫ x, vm x*localGamma μ hQ f w x ∂μ) := by
    rw [← integral_sub hip him]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change v x*localGamma μ hQ f w x=vp x*localGamma μ hQ f w x-vm x*localGamma μ hQ f w x
      rw [hvsplit]
      ring
  have hgint : (∫ x, SobolevSpace.toLp μ hQ f x*localGamma μ hQ η w x ∂μ)=
      (∫ x, SobolevSpace.toLp μ hQ f x*localGamma μ hQ ηp w x ∂μ)-
      (∫ x, SobolevSpace.toLp μ hQ f x*localGamma μ hQ ηm w x ∂μ) := by
    rw [← integral_sub hjp hjm,he]
    apply integral_congr_ae
    filter_upwards [localGamma_sub_left μ hQ ηp ηm w] with x hx
    rw [hx]
    ring
  rw [hvint,hgint,hpint,hmint]
  ring

end RegularPointCoordinates

end

end OAI
