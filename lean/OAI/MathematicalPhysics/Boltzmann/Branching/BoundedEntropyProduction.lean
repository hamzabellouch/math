import OAI.MathematicalPhysics.Boltzmann.Branching.RelativeCutoffConvergence
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionDissipation
import OAI.MathematicalPhysics.Boltzmann.Collision.ScalarEntropyConvex
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyIntegralBalance
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticEntropyErrorLimit

namespace OAI

section

/-! # Collision bounds for a finite approximation under its hot majorant -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem bounded_pair_integrable {μ : Measure X} [IsFiniteMeasure μ]
    {q A : ℝ} (hq : q < 2) (hA : 0 ≤ A) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ A*H q p.2) :
    Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity))) := by
  have hi := ((pairKernel_integrable hq).const_mul (A^2)).comp_snd μ
  apply hi.mono' (pairDensity_measurable hfm).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (pairDensity_nonneg hfn z)]
  exact pairDensity_bound hA hfn z (hfb _) (hfb _)

theorem bounded_cutoff_gain (hcarleman : Published.GPV2009CarlemanInput)
    {μ : Measure X} [SFinite μ] {q A : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hfb : ∀ p, f p ≤ A*H q p.2) (b : ℝ) :
    ∀ᵐ p ∂μ.prod (volume : Measure Velocity),
      KineticCollisionNullSets.gain b f p ≤ (A^2*HotApplication.realBound q)*H q p.2 := by
  have hH : Measurable (fun p : X × Velocity => (A^2*HotApplication.realBound q)*H q p.2) := by
    unfold H singularity transverse
    fun_prop
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_le (KineticCollisionNullSets.measurable_gain hfm b) hH)).mpr
  filter_upwards [] with x
  have h := GainUpperDifference.cutoff_gain_bound hcarleman hq₁ hq₂ hA (le_refl (0:ℝ)) hA
    (hfm.comp (measurable_const.prodMk measurable_id)) measurable_const
    (fun v => hfn (x,v)) (fun _ => le_refl (0:ℝ)) (fun v => hfb (x,v))
    (fun v => by simp) (fun v => by simpa using hfb (x,v)) b
  filter_upwards [h] with v hv
  have hz : CollisionCutoff.gain b (fun _ : Velocity => 0) v = 0 := by
    simp [CollisionCutoff.gain,CollisionCutoff.integrand]
  rw [hz,sub_zero,add_zero] at hv
  simpa only [pow_two,Function.comp_def,id_eq,KineticCollisionNullSets.gain] using hv

theorem bounded_cutoff_loss {μ : Measure X} [IsFiniteMeasure μ]
    {q A b : ℝ} (hq : q < 2) (hA : 0 ≤ A) (hb : 0 ≤ b)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hfb : ∀ p, f p ≤ A*H q p.2) :
    ∀ᵐ p ∂μ.prod (volume : Measure Velocity),
      cutoffLossDensity b f p ≤ (A^2*CutoffLipschitz.frequencyConstant q b)*H q p.2 := by
  have hp := bounded_pair_integrable (μ := μ) hq hA hfm hfn hfb
  filter_upwards [cutoff_loss_ae_eq_frequency hfm hfn hp b] with p he
  rw [he]
  have hν := CutoffLipschitz.frequency_bound hq hb
    (hfm.comp (measurable_const.prodMk measurable_id)) (fun v => hfn (p.1,v))
    (fun v => hfb (p.1,v)) p.2
  have hn := CutoffLipschitz.frequency_nonneg (fun v => hfn (p.1,v)) b p.2
  have hu := mul_le_mul (hfb p) hν hn (mul_nonneg hA (H_nonneg q p.2))
  convert hu using 1
  · simp only [KineticCollisionNullSets.frequency,Function.comp_def,id_eq]
  · ring

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Bounded logarithmic tests recovering nonnegative relative entropy -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness

/-- Outside the bounded logarithmic window use the zero test. At a zero density,
use the negative endpoint, which recovers the Maxwellian contribution. -/
def boundedEntropyTest (n : ℕ) (m u : ℝ) : ℝ :=
  if u = 0 then -(n:ℝ) else if |Real.log (u/m)| ≤ n then Real.log (u/m) else 0

theorem boundedEntropyTest_bound (n : ℕ) (m u : ℝ) :
    |boundedEntropyTest n m u| ≤ n := by
  unfold boundedEntropyTest
  split_ifs with h hlog
  · simp
  · exact hlog
  · simp

theorem entropyDual_boundedEntropyTest_nonneg (n : ℕ) {m u : ℝ}
    (hm : 0 < m) (hu : 0 ≤ u) :
    0 ≤ entropyDual m u (boundedEntropyTest n m u) := by
  unfold boundedEntropyTest
  split_ifs with hz hlog
  · subst u
    dsimp [entropyDual]
    have he : Real.exp (-(n:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
    nlinarith
  · rw [entropyDual_log_ratio hm (lt_of_le_of_ne hu (Ne.symm hz))]
    exact scalarRelativeEntropy_nonneg hm hu
  · simp [entropyDual]

theorem entropyDual_boundedEntropyTest_tendsto {m u : ℝ}
    (hm : 0 < m) (hu : 0 ≤ u) :
    Tendsto (fun n : ℕ => entropyDual m u (boundedEntropyTest n m u)) atTop
      (𝓝 (scalarRelativeEntropy m u)) := by
  by_cases hz : u = 0
  · subst u
    simpa [boundedEntropyTest,scalarRelativeEntropy,Function.comp_def] using
      (entropyDual_zero_tendsto m).comp tendsto_natCast_atTop_atTop
  · have he : (fun n : ℕ => entropyDual m u (boundedEntropyTest n m u)) =ᶠ[atTop]
        (fun _ => scalarRelativeEntropy m u) := by
      filter_upwards [eventually_ge_atTop (Nat.ceil |Real.log (u/m)|)] with n hn
      have hlog : |Real.log (u/m)| ≤ (n:ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hn)
      simpa [boundedEntropyTest,hz,hlog] using
        entropyDual_log_ratio hm (lt_of_le_of_ne hu (Ne.symm hz))
    exact tendsto_const_nhds.congr' he.symm

end BoltzmannNonuniqueness

end

end

section

/-! # Entropy production for a positive bounded finite approximation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem bounded_log_gainLoss_integrable (hcarleman : Published.GPV2009CarlemanInput)
    {μ : Measure X} [IsFiniteMeasure μ] {q A B δ b : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 < δ) (hb : 0 ≤ b)
    {f u : X × Velocity → ℝ} (hfm : Measurable f) (hum : Measurable u)
    (hfn : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ A*H q p.2)
    (hul : ∀ p, δ*Real.exp (-2*‖p.2‖^2) ≤ u p) (hub : ∀ p, u p ≤ B*H q p.2) :
    Integrable (fun p => Real.log (u p/maxwellian p.2)*KineticCollisionNullSets.gain b f p)
      (μ.prod volume) ∧
    Integrable (fun p => Real.log (u p/maxwellian p.2)*cutoffLossDensity b f p) (μ.prod volume) := by
  constructor
  · apply kinetic_log_product_integrable hq₁ hq₂ hB
      (mul_nonneg (sq_nonneg A) (HotApplication.realBound_pos q).le) hδ hum
      (KineticCollisionNullSets.measurable_gain hfm b) hul hub
    filter_upwards [bounded_cutoff_gain hcarleman hq₁ hq₂ hA hfm hfn hfb b] with p hp
    simpa only [abs_of_nonneg (cutoffGainDensity_nonneg hfn b p)] using hp
  · apply kinetic_log_product_integrable hq₁ hq₂ hB
      (mul_nonneg (sq_nonneg A) (CutoffLipschitz.frequencyConstant_nonneg hb q)) hδ hum
      (cutoffLossDensity_measurable hfm b) hul hub
    filter_upwards [bounded_cutoff_loss hq₂ hA hb hfm hfn hfb] with p hp
    simpa only [abs_of_nonneg (cutoffLossDensity_nonneg hfn b p)] using hp

theorem bounded_positive_entropy_production (hcarleman : Published.GPV2009CarlemanInput)
    {μ : Measure X} [IsFiniteMeasure μ] {q A δ b : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hδ : 0 < δ) (hb : 0 ≤ b)
    {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hfl : ∀ p, δ*Real.exp (-2*‖p.2‖^2) ≤ f p) (hfb : ∀ p, f p ≤ A*H q p.2) :
    (∫ p, Real.log (f p/maxwellian p.2)*collisionSource b f p ∂μ.prod volume) ≤ 0 := by
  have hfp : ∀ p, 0 < f p := fun p => (mul_pos hδ (Real.exp_pos _)).trans_le (hfl p)
  have hfn : ∀ p, 0 ≤ f p := fun p => (hfp p).le
  have hpair := bounded_pair_integrable (μ := μ) hq₂ hA hfm hfn hfb
  have hgL := bounded_log_gainLoss_integrable (μ := μ) hcarleman hq₁ hq₂ hA hA hδ hb hfm hfm hfn hfb hfl hfb
  have hlog : Measurable (fun p : X × Velocity => Real.log (f p/maxwellian p.2)) := by
    have hm : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
    exact (hfm.div hm).log
  have hS : MeasurableSet {z : (X × (Velocity × Velocity)) × Sphere | ‖z.1.2.1-z.1.2.2‖ < b} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hprei := (preRate_integrable hfm hfn hpair).indicator hS
  have hposti := (postRate_integrable hfm hfn hpair).indicator hS
  have hpren : ∀ z, 0 ≤ truncatedPreRate b f z := fun z =>
    Set.indicator_nonneg (fun z _ => preRate_nonneg hfn z) z
  have hpostn : ∀ z, 0 ≤ truncatedPostRate b f z := fun z =>
    Set.indicator_nonneg (fun z _ => preRate_nonneg hfn (scatterTriple z)) z
  have hpre := collision_test_integrable_of_marginal (truncatedPreRate_measurable hfm b)
    hpren hprei hlog (by simpa only [← cutoffLoss_eq_marginal] using hgL.2)
  have hpost := collision_test_integrable_of_marginal (truncatedPostRate_measurable hfm b)
    hpostn hposti hlog (by simpa only [← cutoffGain_eq_marginal] using hgL.1)
  have hprod := cutoff_relative_entropy_nonpositive b f hfp hpre hpost
  have hloss := cutoff_loss_ae_eq_frequency hfm hfn hpair b
  have hLi : Integrable (fun p => Real.log (f p/maxwellian p.2)*
      (f p*KineticCollisionNullSets.frequency b f p)) (μ.prod volume) := by
    apply hgL.2.congr
    filter_upwards [hloss] with p hp
    rw [hp]
  calc
    _ = (∫ p, Real.log (f p/maxwellian p.2)*KineticCollisionNullSets.gain b f p ∂μ.prod volume)-
        (∫ p, Real.log (f p/maxwellian p.2)*cutoffLossDensity b f p ∂μ.prod volume) := by
      simp_rw [collisionSource,mul_sub]
      rw [integral_sub hgL.1 hLi]
      congr 1
      apply integral_congr_ae
      filter_upwards [hloss] with p hp
      rw [hp]
    _ ≤ 0 := hprod

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
