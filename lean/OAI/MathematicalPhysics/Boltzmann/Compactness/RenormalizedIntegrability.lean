import OAI.MathematicalPhysics.Boltzmann.Branching.LossIntegrability
import OAI.MathematicalPhysics.Boltzmann.Branching.PublishedInputs
import OAI.MathematicalPhysics.Boltzmann.Branching.RenormalizationBounds
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionWeakMarginals
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianEstimates
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityCutoffEntropyError
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyIntegralBalance
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticDensityMeasurable
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Jets.JetProfiles
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

namespace OAI

section

/-! # Measurability and integrability of the renormalized collision source -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Renormalization

variable {X : Type*} [MeasurableSpace X]

theorem measurable_derivative_comp (β : Renormalization) {f : X → ℝ}
    (hfm : Measurable f) (hfn : ∀ x, 0 ≤ f x) :
    Measurable (fun x => derivWithin β.toFun (Ici 0) (f x)) := by
  have hc := β.regular.continuousOn_derivWithin (uniqueDiffOn_Ici 0) (le_refl 1)
  exact (continuousOn_iff_continuous_domRestrict.mp hc).measurable.comp
    (hfm.subtype_mk (h := hfn))

theorem derivative_mul_integrable (β : Renormalization) {μ : Measure X}
    {f r : X → ℝ} (hfm : Measurable f) (hfn : ∀ x, 0 ≤ f x) (hri : Integrable r μ) :
    Integrable (fun x => derivWithin β.toFun (Ici 0) (f x)*r x) μ := by
  obtain ⟨C,hC,hb⟩ := β.derivative_bound
  apply hri.bdd_mul (c := C) (β.measurable_derivative_comp hfm hfn).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs]
  exact (hb (f x) (hfn x)).trans (div_le_self hC (by linarith only [hfn x]))

end BoltzmannNonuniqueness.Renormalization

end

end

section

/-! # Replacing a positive Maxwellian normalizer on a bounded velocity window -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.Compactness

theorem change_normalizer_bound {A u m c : ℝ} (hA : 0 ≤ A) (hu : 0 ≤ u)
    (hc : 0 < c) (hm : c ≤ m) :
    A/(1+u) ≤ (1+1/c)*(A/(1+u/m)) := by
  have hm0 : 0 < m := hc.trans_le hm
  have hD : 0 < 1+u/m := by positivity
  have hU : 0 < 1+u := by positivity
  have hd : 1+u/m ≤ (1+1/c)*(1+u) := by
    have ht : u/m ≤ u/c := div_le_div_of_nonneg_left hu hc hm
    have hp : 0 ≤ 1/c := (one_div_pos.mpr hc).le
    have he : u/c = u*(1/c) := by ring
    rw [he] at ht
    nlinarith
  apply (div_le_iff₀ hU).mpr
  calc
    A = (A/(1+u/m))*(1+u/m) := (div_mul_cancel₀ A hD.ne').symm
    _ ≤ (A/(1+u/m))*((1+1/c)*(1+u)) :=
      mul_le_mul_of_nonneg_left hd (div_nonneg hA hD.le)
    _ = _ := by ring

theorem uniformIntegrable_change_normalizer
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a u : ℕ → X → ℝ} {m : X → ℝ} {c : ℝ}
    (ham : ∀ n, Measurable (a n)) (hum : ∀ n, Measurable (u n))
    (ha : ∀ n x, 0 ≤ a n x) (hu : ∀ n x, 0 ≤ u n x)
    (hc : 0 < c) (hm : ∀ᵐ x ∂μ, c ≤ m x)
    (hi : UniformIntegrable (fun n x => a n x/(1+u n x/m x)) 1 μ) :
    UniformIntegrable (fun n x => a n x/(1+u n x)) 1 μ := by
  let K : ℝ := 1+1/c
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hKi := uniformIntegrable_of_bounded_multiplier hi (a := fun _ => K)
    measurable_const (⟨K,hK⟩ : ℝ≥0) (fun _ => (abs_of_nonneg hK).le)
  apply uniformIntegrable_abs_le hKi
    (fun n => ((ham n).div (measurable_const.add (hum n))).aestronglyMeasurable)
  intro n
  filter_upwards [hm] with x hx
  change |a n x/(1+u n x)| ≤ _
  rw [abs_of_nonneg (div_nonneg (ha n x) (by linarith [hu n x]))]
  exact change_normalizer_bound (ha n x) (hu n x) hc hx

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Integrability of the weak renormalized equation on finite intervals -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

namespace Renormalization

variable {X : Type*} [MeasurableSpace X]

theorem weighted_measurable (β : Renormalization) {f m : X → ℝ}
    (hfm : Measurable f) (hmm : Measurable m) (hfn : ∀ x, 0 ≤ f x) (hm : ∀ x, 0 < m x) :
    Measurable (fun x => m x*β.toFun (f x/m x)) := by
  have hq := hfm.div hmm
  have hn : ∀ x, f x/m x ∈ Ici 0 := fun x => div_nonneg (hfn x) (hm x).le
  have hb := (continuousOn_iff_continuous_domRestrict.mp β.regular.continuousOn).measurable.comp
    (hq.subtype_mk (h := hn))
  exact hmm.mul hb

theorem weighted_integrable (β : Renormalization) {μ : Measure X} {f m : X → ℝ}
    (hfm : Measurable f) (hmm : Measurable m) (hfn : ∀ x, 0 ≤ f x) (hm : ∀ x, 0 < m x)
    (hfi : Integrable f μ) : Integrable (fun x => m x*β.toFun (f x/m x)) μ := by
  obtain ⟨C,hC⟩ := β.exists_lipschitz
  apply (hfi.const_mul (C:ℝ)).mono' (β.weighted_measurable hfm hmm hfn hm).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs] using weighted_abs_bound hC (hm x) (hfn x))

end Renormalization

theorem renormalizedIntegrand_integrable {T : ℝ} {F : Evolution}
    (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t p, 0 ≤ F t p)
    (hFi : Integrable (fun z : ℝ × Phase => F z.1 z.2)
      ((volume.restrict (Icc 0 T)).prod volume))
    (hQi : Integrable (fun z : ℝ × Phase => collision (F z.1) z.2.1 z.2.2)
      ((volume.restrict (Icc 0 T)).prod volume)) (β : Renormalization) (φ : KineticTest) :
    IntegrableOn (renormalizedIntegrand F β φ) (boundedTimes T) := by
  let μ : Measure (ℝ × Phase) := (volume.restrict (Icc 0 T)).prod volume
  have hmm : Measurable (fun z : ℝ × Phase => maxwellian z.2.2) := by
    unfold maxwellian
    fun_prop
  have hq := hFm.div hmm
  have hn : ∀ z : ℝ × Phase, 0 ≤ F z.1 z.2/maxwellian z.2.2 :=
    fun z => div_nonneg (hFn z.1 z.2) (maxwellian_pos z.2.2).le
  have hwi := β.weighted_integrable hFm hmm (fun z => hFn z.1 z.2)
    (fun z => maxwellian_pos z.2.2) hFi
  have hri := β.derivative_mul_integrable hq hn hQi
  obtain ⟨C,_hC,hb⟩ := φ.bounded_on_time T
  have ht : ∀ᵐ z : ℝ × Phase ∂μ, z.1 ∈ Icc 0 T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  have hwb : ∀ᵐ z : ℝ × Phase ∂μ, ‖φ.transportDerivative z.1 z.2‖ ≤ C := by
    filter_upwards [ht] with z hz
    simpa only [Real.norm_eq_abs] using (hb z.1 hz z.2).2
  have hrb : ∀ᵐ z : ℝ × Phase ∂μ, ‖φ.toFun z.1 z.2.1 z.2.2‖ ≤ C := by
    filter_upwards [ht] with z hz
    simpa only [Real.norm_eq_abs] using (hb z.1 hz z.2).1
  have hi := (hwi.mul_bdd φ.measurable_transportDerivative.aestronglyMeasurable hwb).add
    (hri.mul_bdd φ.measurable_toFun.aestronglyMeasurable hrb)
  change Integrable (renormalizedIntegrand F β φ) _
  rw [← phaseInterval_measure]
  exact hi

end BoltzmannNonuniqueness

end

end

section

/-! # Renormalized loss is controlled by linear velocity moments -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem density_over_renormalization_le {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m) :
    0 ≤ a/(1+a/m) ∧ a/(1+a/m) ≤ m := by
  have h : 0 < 1+a/m := by positivity
  refine ⟨div_nonneg ha h.le,(div_le_iff₀ h).mpr ?_⟩
  have he : m*(1+a/m) = m+a := by field_simp
  rw [he]
  linarith

theorem renormalized_loss_bound (f : X × Velocity → ℝ) (x : X) (v : Velocity)
    (hn : 0 ≤ f (x,v)) (hf : Integrable (fun w => f (x,w)))
    (hm : Integrable (fun w => ‖w‖*f (x,w))) :
    |lossDensity f (x,v)/(1+f (x,v)/maxwellian v)| ≤
      2*Real.pi*maxwellian v*(‖v‖*(∫ w, |f (x,w)|)+(∫ w, ‖w‖*|f (x,w)|)) := by
  let F : Density := fun z => f (x,z.2)
  have hl : lossDensity f (x,v) = f (x,v)*frequency F 0 v :=
    loss_eq_mul_frequency F 0 v (integrable_loss_of_moments F 0 v hf hm)
  have hb := density_over_renormalization_le hn (maxwellian_pos v)
  have hν := abs_frequency_le F 0 v hf hm
  rw [hl]
  calc
    |f (x,v)*frequency F 0 v/(1+f (x,v)/maxwellian v)| =
        (f (x,v)/(1+f (x,v)/maxwellian v))*|frequency F 0 v| := by
      rw [mul_div_right_comm,abs_mul,abs_of_nonneg hb.1]
    _ ≤ maxwellian v*|frequency F 0 v| :=
      mul_le_mul_of_nonneg_right hb.2 (abs_nonneg _)
    _ ≤ maxwellian v*(2*Real.pi*(‖v‖*(∫ w, |f (x,w)|)+(∫ w, ‖w‖*|f (x,w)|))) :=
      mul_le_mul_of_nonneg_left hν (maxwellian_pos v).le
    _ = _ := by ring

theorem integrable_maxwellian_firstMoment : Integrable (fun v : Velocity => ‖v‖*maxwellian v) := by
  have h := (JetGaussianMoments.moment_integrable (by norm_num : (0:ℝ) < 1/2)).const_mul
    ((2*Real.pi)^(-(3/2:ℝ)))
  convert h using 1
  ext v
  unfold maxwellian JetGaussianMoments.kernel
  rw [show -‖v‖^2/2 = -(1/2:ℝ)*‖v‖^2 by ring]
  ring

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Separate integrability of the renormalized physical loss -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem renormalized_loss_integrable {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hf : Integrable f (μ.prod volume))
    (hm : Integrable (fun p => ‖p.2‖*f p) (μ.prod volume)) :
    Integrable (fun p => lossDensity f p/(1+f p/maxwellian p.2)) (μ.prod volume) := by
  let m₀ x := ∫ v, |f (x,v)|
  let m₁ x := ∫ v, ‖v‖*|f (x,v)|
  have h₀ : Integrable m₀ μ := hf.abs.integral_prod_left
  have hma : Integrable (fun p : X × Velocity => ‖p.2‖*|f p|) (μ.prod volume) := by
    simpa only [Real.norm_eq_abs,abs_mul,abs_norm] using hm.norm
  have h₁ : Integrable m₁ μ := hma.integral_prod_left
  have hbound : Integrable (fun p : X × Velocity =>
      2*Real.pi*maxwellian p.2*(‖p.2‖*m₀ p.1+m₁ p.1)) (μ.prod volume) := by
    have h := ((h₀.mul_prod integrable_maxwellian_firstMoment).add
      (h₁.mul_prod integrable_maxwellian)).const_mul (2*Real.pi)
    convert h using 1
    ext p
    simp only [Pi.add_apply]
    ring
  have hM : Measurable (fun p : X × Velocity => maxwellian p.2) := by
    unfold maxwellian
    fun_prop
  apply hbound.mono' ((lossDensity_measurable hfm).div (measurable_const.add (hfm.div hM))).aestronglyMeasurable
  have hfa := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (volume : Measure Velocity))).ae hf.prod_right_ae
  have hma' := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (volume : Measure Velocity))).ae hm.prod_right_ae
  filter_upwards [hfa,hma'] with p hp hmp
  simpa only [Real.norm_eq_abs,Pi.div_apply,Pi.add_apply,m₀,m₁,Prod.mk.eta] using renormalized_loss_bound f p.1 p.2 (hfn p) hp hmp

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Entropy and energy make normalized physical loss uniformly integrable -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.CollisionCompactness
open PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem renormalized_loss_uniformIntegrable {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n p => lossDensity (f n) p/(1+f n p/maxwellian p.2)) 1 (μ.prod volume) := by
  let m (n : ℕ) (x : X) := ∫ v, linearMoment (f n) (x,v)
  let g (v : Velocity) := 2*Real.pi*maxwellian v*(1+‖v‖)
  have hm n : Measurable (m n) := (linearMoment_measurable (hfm n)).stronglyMeasurable.integral_prod_right'.measurable
  have hmui : UniformIntegrable m 1 μ := linearMoment_marginal_uniformIntegrable hfm hf hi hb
  have hgm : Measurable g := by dsimp [g,maxwellian]; fun_prop
  have hgi : Integrable g := by
    have h := (integrable_maxwellian.add integrable_maxwellian_firstMoment).const_mul (2*Real.pi)
    convert h using 1
    funext v
    dsimp only [g,Pi.add_apply]
    ring
  have hui := Compactness.uniformIntegrable_tensor hm hmui hgm hgi
  have hM : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
  apply uniformIntegrable_mono_nonneg hui
    (fun n => ((lossDensity_measurable (hfm n)).div
      (measurable_const.add ((hfm n).div hM))).aestronglyMeasurable)
    (fun n => ae_of_all _ (fun p => div_nonneg (lossDensity_nonneg (hf n) p)
      (le_of_lt (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (hf n p) (maxwellian_pos p.2).le)))))
  intro n
  have hfi := integrable_of_entropyGauge (hfm n) (hf n) (hi n)
  have hli := linearMoment_integrable (hfm n) (hf n) (hi n)
  have hv : Integrable (fun p => ‖p.2‖*f n p) (μ.prod volume) := by
    convert hli.sub hfi using 1
    funext p
    dsimp only [linearMoment,Pi.sub_apply]
    ring
  have h0 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (volume : Measure Velocity))).ae hfi.prod_right_ae
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (volume : Measure Velocity))).ae hv.prod_right_ae
  have h2 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (volume : Measure Velocity))).ae hli.prod_right_ae
  filter_upwards [h0,h1,h2] with p hp0 hp1 hp2
  have hbound := renormalized_loss_bound (f n) p.1 p.2 (hf n p) hp0 hp1
  have hm0 : (∫ v, |f n (p.1,v)|) ≤ m n p.1 := by
    apply integral_mono hp0.abs hp2
    intro v
    change |f n (p.1,v)| ≤ (1+‖v‖)*f n (p.1,v)
    rw [abs_of_nonneg (hf n _)]
    nlinarith [norm_nonneg v,hf n (p.1,v)]
  have hma : Integrable (fun v => ‖v‖*|f n (p.1,v)|) := by
    simpa only [abs_mul,abs_norm,Real.norm_eq_abs] using hp1.norm
  have hm1 : (∫ v, ‖v‖*|f n (p.1,v)|) ≤ m n p.1 := by
    apply integral_mono hma hp2
    intro v
    change ‖v‖*|f n (p.1,v)| ≤ (1+‖v‖)*f n (p.1,v)
    rw [abs_of_nonneg (hf n _)]
    nlinarith [hf n (p.1,v)]
  calc
    _ ≤ |lossDensity (f n) p/(1+f n p/maxwellian p.2)| := le_abs_self _
    _ ≤ 2*Real.pi*maxwellian p.2*(‖p.2‖*(∫ v, |f n (p.1,v)|)+(∫ v, ‖v‖*|f n (p.1,v)|)) := hbound
    _ ≤ 2*Real.pi*maxwellian p.2*(‖p.2‖*m n p.1+m n p.1) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hm0 (norm_nonneg _)) hm1)
        (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (maxwellian_pos _).le)
    _ = m n p.1*g p.2 := by dsimp only [g]; ring

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Entropy production controls the separately renormalized gain -/
noncomputable section
open scoped ENNReal
namespace BoltzmannNonuniqueness

theorem gain_le_loss_add_extendedProduction {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ENNReal.ofReal A ≤ 2*ENNReal.ofReal B +
      ENNReal.ofReal (2/Real.log 2)*extendedEntropyProduction A B := by
  have hC : 0 < (2:ℝ)/Real.log 2 := div_pos (by norm_num) (Real.log_pos (by norm_num))
  by_cases ha : A = 0
  · simp [ha]
  have hapos : 0 < A := lt_of_le_of_ne hA (Ne.symm ha)
  by_cases hb : B = 0
  · simp [extendedEntropyProduction,ha,hb,ne_of_gt (ENNReal.ofReal_pos.mpr hC)]
  have hbpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hb)
  have h := ENNReal.ofReal_le_ofReal (Published.gain_le_loss_add_entropy hapos hbpos)
  have hD := Published.entropyProduction_nonneg hapos hbpos
  rw [extendedEntropyProduction,ite_eq_right (by simp [ha]),ite_eq_left ⟨hapos,hbpos⟩]
  have he : ENNReal.ofReal (2*B+(2/Real.log 2)*Published.entropyProduction A B) =
      2*ENNReal.ofReal B+ENNReal.ofReal (2/Real.log 2)*ENNReal.ofReal (Published.entropyProduction A B) := by
    rw [ENNReal.ofReal_add (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB) (mul_nonneg hC.le hD),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_mul hC.le,ENNReal.ofReal_ofNat]
  rw [he] at h
  simpa only [Published.entropyProduction] using h

theorem weighted_gain_le_loss_add_extendedProduction {A B k θ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hk : 0 ≤ k) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    ENNReal.ofReal (k*θ*A) ≤ 2*ENNReal.ofReal (k*θ*B) +
      ENNReal.ofReal (2/Real.log 2)*ENNReal.ofReal k*extendedEntropyProduction A B := by
  have hg := gain_le_loss_add_extendedProduction hA hB
  have hθ' : ENNReal.ofReal θ ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hθone
  simp only [ENNReal.ofReal_mul (mul_nonneg hk hθ),ENNReal.ofReal_mul hk]
  calc
    ENNReal.ofReal k*ENNReal.ofReal θ*ENNReal.ofReal A ≤
        ENNReal.ofReal k*ENNReal.ofReal θ*(2*ENNReal.ofReal B+
          ENNReal.ofReal (2/Real.log 2)*extendedEntropyProduction A B) := by gcongr
    _ = 2*(ENNReal.ofReal k*ENNReal.ofReal θ*ENNReal.ofReal B)+
        ENNReal.ofReal (2/Real.log 2)*ENNReal.ofReal k*ENNReal.ofReal θ*extendedEntropyProduction A B := by ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      calc
        _ = (ENNReal.ofReal (2/Real.log 2)*ENNReal.ofReal k*extendedEntropyProduction A B)*ENNReal.ofReal θ := by ring
        _ ≤ (ENNReal.ofReal (2/Real.log 2)*ENNReal.ofReal k*extendedEntropyProduction A B)*1 := by gcongr
        _ = _ := mul_one _

end BoltzmannNonuniqueness

end

end

section

/-! # Uniform integrability for the manuscript's renormalizations -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace BoltzmannNonuniqueness.Renormalization
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem weighted_uniformIntegrable (β : Renormalization) {f : ℕ → X → ℝ} {m : X → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hmm : Measurable m)
    (hfn : ∀ n x, 0 ≤ f n x) (hm : ∀ x, 0 < m x) (hf : UniformIntegrable f 1 μ) :
    UniformIntegrable (fun n x => m x*β.toFun (f n x/m x)) 1 μ := by
  obtain ⟨C,hC⟩ := β.exists_lipschitz
  have hc := Compactness.uniformIntegrable_of_bounded_multiplier hf
    (a := fun _ => (C:ℝ)) measurable_const C (fun _ => by simp)
  have hmeas n := (β.weighted_measurable (hfm n) hmm (hfn n) hm).aestronglyMeasurable (μ := μ)
  have hb n : ∀ᵐ x ∂μ, ‖m x*β.toFun (f n x/m x)‖ₑ ≤ ‖(C:ℝ)*f n x‖ₑ := by
    filter_upwards [] with x
    apply enorm_le_iff_norm_le.mpr
    rw [Real.norm_eq_abs,Real.norm_of_nonneg (mul_nonneg C.coe_nonneg (hfn n x))]
    exact weighted_abs_bound hC (hm x) (hfn n x)
  obtain ⟨hu,B,hB⟩ := hc
  exact ⟨hu.ae_mono hmeas hb,B,fun n => (eLpNorm_mono_enorm_ae (hmeas n) (hb n)).trans (hB n)⟩

theorem derivative_uniformIntegrable (β : Renormalization) {f r : ℕ → X → ℝ} {m : X → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hmm : Measurable m)
    (hfn : ∀ n x, 0 ≤ f n x) (hm : ∀ x, 0 < m x)
    (hr : UniformIntegrable (fun n x => r n x/(1+f n x/m x)) 1 μ) :
    UniformIntegrable (fun n x => derivWithin β.toFun (Ici 0) (f n x/m x)*r n x) 1 μ := by
  obtain ⟨C,hC,hb⟩ := β.derivative_bound
  let a : ℕ → X → ℝ := fun n x => (1+f n x/m x)*derivWithin β.toFun (Ici 0) (f n x/m x)
  have hz n x : 0 ≤ f n x/m x := div_nonneg (hfn n x) (hm x).le
  have hd n x : 0 < 1+f n x/m x := by linarith [hz n x]
  have ha n : Measurable (a n) :=
    (measurable_const.add ((hfm n).div hmm)).mul
      (β.measurable_derivative_comp ((hfm n).div hmm) (hz n))
  have hbound n x : |a n x| ≤ (⟨C,hC⟩ : ℝ≥0) := by
    dsimp only [a,NNReal.coe_mk]
    rw [abs_mul,abs_of_pos (hd n x),mul_comm]
    exact (le_div_iff₀ (hd n x)).mp (hb (f n x/m x) (hz n x))
  have h := Compactness.uniformIntegrable_of_varying_multiplier hr ha ⟨C,hC⟩ hbound
  apply h.ae_eq
  intro n
  filter_upwards [] with x
  dsimp only [a]
  field_simp [(hd n x).ne']

end BoltzmannNonuniqueness.Renormalization

end

end

section

/-! # The renormalization chain rule on nonnegative absolutely continuous paths -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Renormalization

theorem chain_rule (β : Renormalization) {a b : ℝ} (hab : a ≤ b) {F r : ℝ → ℝ}
    (hF : AbsolutelyContinuousOnInterval F a b)
    (hFn : ∀ t ∈ Icc a b, 0 ≤ F t)
    (hr : ∀ᵐ t, t ∈ Icc a b → HasDerivAt F (r t) t) :
    (∫ t in a..b, derivWithin β.toFun (Ici 0) (F t)*r t) =
      β.toFun (F b)-β.toFun (F a) := by
  obtain ⟨C,hC⟩ := β.exists_lipschitz
  have hc : AbsolutelyContinuousOnInterval (fun t => β.toFun (F t)) a b :=
    hC.comp_absolutelyContinuousOnInterval
      (fun t ht => hFn t (by simpa only [uIcc_of_le hab] using ht)) hF
  rw [← hc.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hr,Measure.ae_ne (volume : Measure ℝ) b] with t hrt htb ht
  have ht' : t ∈ Ioc a b := by simpa only [uIoc_of_le hab] using ht
  have htcc : t ∈ Icc a b := ⟨ht'.1.le,ht'.2⟩
  have hβ := (β.regular.differentiableOn (by norm_num) (F t) (hFn t htcc)).hasDerivWithinAt
  have hd := hβ.scomp t (hrt htcc).hasDerivWithinAt hFn
  have hda := hd.hasDerivAt (Icc_mem_nhds ht'.1 (lt_of_le_of_ne ht'.2 htb))
  simpa only [Function.comp_def,smul_eq_mul,mul_comm] using hda.deriv.symm


theorem weighted_chain_rule (β : Renormalization) {a b m : ℝ} (hab : a ≤ b)
    (hm : 0 < m) {F r : ℝ → ℝ} (hF : AbsolutelyContinuousOnInterval F a b)
    (hFn : ∀ t ∈ Icc a b, 0 ≤ F t)
    (hr : ∀ᵐ t, t ∈ Icc a b → HasDerivAt F (r t) t) :
    (∫ t in a..b, derivWithin β.toFun (Ici 0) (F t/m)*r t) =
      m*β.toFun (F b/m)-m*β.toFun (F a/m) := by
  have hF' : AbsolutelyContinuousOnInterval (fun t => F t/m) a b := by
    simpa only [div_eq_mul_inv,mul_comm] using
      AbsolutelyContinuousOnInterval.const_mul m⁻¹ hF
  have hr' : ∀ᵐ t, t ∈ Icc a b → HasDerivAt (fun t => F t/m) (r t/m) t := by
    filter_upwards [hr] with t ht hmem
    exact (ht hmem).div_const m
  have he := congrArg (fun x : ℝ => m*x) (β.chain_rule hab hF'
    (fun t ht => div_nonneg (hFn t ht) hm.le) hr')
  rw [← intervalIntegral.integral_const_mul] at he
  have hi : (fun t => m*(derivWithin β.toFun (Ici 0) (F t/m)*(r t/m))) =
      (fun t => derivWithin β.toFun (Ici 0) (F t/m)*r t) := by
    funext t
    field_simp
  rw [hi] at he
  exact he.trans (by ring)

end BoltzmannNonuniqueness.Renormalization

end

end

section

/-! # A vanishing entropy cost for truncating gain by a multiple of loss -/
noncomputable section
open Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness

theorem gain_le_scaled_loss_add_entropy {A B R : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hR : 2 ≤ R) :
    A ≤ R*B+(2/Real.log R)*Published.entropyProduction A B := by
  have hRp : 0 < R := by linarith
  have hlR : 0 < Real.log R := Real.log_pos (by linarith)
  have hD := Published.entropyProduction_nonneg hA hB
  by_cases h : A ≤ R*B
  · exact h.trans (le_add_of_nonneg_right (mul_nonneg (by positivity) hD))
  · have hAB : 2*B ≤ A := by nlinarith
    have hr : R ≤ A/B := (le_div_iff₀ hB).mpr (le_of_not_ge h)
    have hl : Real.log R ≤ Real.log (A/B) := Real.log_le_log hRp hr
    have hhalf : A/2 ≤ A-B := by linarith
    have hb : (A/2)*Real.log R ≤ Published.entropyProduction A B := by
      exact mul_le_mul hhalf hl hlR.le (by linarith)
    have he : A ≤ (2/Real.log R)*Published.entropyProduction A B := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hlR).mpr
      nlinarith
    exact he.trans (le_add_of_nonneg_left (mul_nonneg hRp.le hB.le))

theorem gain_le_scaled_loss_add_extendedProduction {A B R : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 2 ≤ R) :
    ENNReal.ofReal A ≤ ENNReal.ofReal R*ENNReal.ofReal B +
      ENNReal.ofReal (2/Real.log R)*extendedEntropyProduction A B := by
  have hlR : 0 < Real.log R := Real.log_pos (by linarith)
  have hC : 0 < 2/Real.log R := by positivity
  by_cases ha : A = 0
  · simp [ha]
  by_cases hb : B = 0
  · simp [extendedEntropyProduction,ha,hb,ne_of_gt (ENNReal.ofReal_pos.mpr hC)]
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm ha)
  have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hb)
  have hd := Published.entropyProduction_nonneg hAp hBp
  have h := ENNReal.ofReal_le_ofReal (gain_le_scaled_loss_add_entropy hAp hBp hR)
  rw [ENNReal.ofReal_add (mul_nonneg (by linarith) hB) (mul_nonneg hC.le hd),
    ENNReal.ofReal_mul (by linarith : 0 ≤ R),ENNReal.ofReal_mul hC.le] at h
  simpa only [extendedEntropyProduction,ha,false_and,ite_false,
    ite_eq_left (And.intro hAp hBp),Published.entropyProduction] using h

theorem scaled_entropy_cost_tendsto :
    Tendsto (fun R : ℝ => 2/Real.log R) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop Real.tendsto_log_atTop

end BoltzmannNonuniqueness

end

end

section

/-! # Integrability of the full collision pre-rate after renormalization -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness

local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

def normalizedPreRate (f : X × Velocity → ℝ)
    (z : (X × Velocity) × (Velocity × Sphere)) : ℝ :=
  preRate f (collisionGrouping.symm z)/(1+f z.1/maxwellian z.1.2)

def normalizedPostRate (f : X × Velocity → ℝ)
    (z : (X × Velocity) × (Velocity × Sphere)) : ℝ :=
  postRate f (collisionGrouping.symm z)/(1+f z.1/maxwellian z.1.2)

theorem normalizedPreRate_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (normalizedPreRate f) := by
  apply ((preRate_measurable hf).comp collisionGrouping.symm.measurable).div
  apply measurable_const.add
  apply (hf.comp measurable_fst).div
  unfold maxwellian
  fun_prop

theorem normalizedPostRate_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (normalizedPostRate f) := by
  apply (((preRate_measurable hf).comp scatterTriple_measurable).comp collisionGrouping.symm.measurable).div
  apply measurable_const.add
  apply (hf.comp measurable_fst).div
  unfold maxwellian
  fun_prop

theorem normalizedPreRate_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (z) :
    0 ≤ normalizedPreRate f z :=
  div_nonneg (preRate_nonneg hf _) (by have := hf z.1; have := (maxwellian_pos z.1.2).le; positivity)

theorem normalizedPreRate_integral (f : X × Velocity → ℝ) (p : X × Velocity) :
    (∫ q, normalizedPreRate f (p,q) ∂((volume : Measure Velocity).prod sphereArea)) =
      lossDensity f p/(1+f p/maxwellian p.2) := by
  unfold normalizedPreRate lossDensity
  dsimp only
  rw [integral_div]

variable {μ : Measure X} [SFinite μ]

theorem normalizedPreRate_integrable {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hf : Integrable f (μ.prod volume))
    (hm : Integrable (fun p => ‖p.2‖*f p) (μ.prod volume)) :
    Integrable (normalizedPreRate f) ((μ.prod volume).prod ((volume : Measure Velocity).prod sphereArea)) := by
  apply (integrable_prod_iff (normalizedPreRate_measurable hfm).aestronglyMeasurable).mpr
  constructor
  · have hfa := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (volume : Measure Velocity))).ae hf.prod_right_ae
    have hma := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (volume : Measure Velocity))).ae hm.prod_right_ae
    filter_upwards [hfa,hma] with p hp hmp
    change Integrable (fun q : Velocity × Sphere =>
      (collisionKernel p.2 q.1 q.2*f p*f (p.1,q.1))/(1+f p/maxwellian p.2)) _
    exact (integrable_loss_of_moments (fun z : Phase => f (p.1,z.2)) 0 p.2 hp hmp).div_const _
  · have h := renormalized_loss_integrable hfm hfn hf hm
    convert h using 1
    ext p
    simp_rw [Real.norm_of_nonneg (normalizedPreRate_nonneg hfn _)]
    exact normalizedPreRate_integral f p

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Finite entropy production gives the separately integrable gain -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness

local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem normalizedPostRate_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (z) :
    0 ≤ normalizedPostRate f z := by
  apply div_nonneg (preRate_nonneg hf _)
  have := hf z.1
  have := (maxwellian_pos z.1.2).le
  positivity

theorem normalizedPostRate_entropy_bound {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : (X × Velocity) × (Velocity × Sphere)) :
    ‖normalizedPostRate f z‖ₑ ≤ 2*‖normalizedPreRate f z‖ₑ+
      ENNReal.ofReal (2/Real.log 2)*extendedEntropyProduction
        (postRate f (collisionGrouping.symm z)) (preRate f (collisionGrouping.symm z)) := by
  let d := 1+f z.1/maxwellian z.1.2
  have hd : 1 ≤ d := le_add_of_nonneg_right (div_nonneg (hf _) (maxwellian_pos _).le)
  have hdp : 0 < d := zero_lt_one.trans_le hd
  have hθ : 0 ≤ d⁻¹ := inv_nonneg.mpr hdp.le
  have hθ1 : d⁻¹ ≤ 1 := (inv_le_one₀ hdp).mpr hd
  have hA : 0 ≤ postRate f (collisionGrouping.symm z) := preRate_nonneg hf _
  have hB := preRate_nonneg hf (collisionGrouping.symm z)
  have h := weighted_gain_le_loss_add_extendedProduction hA hB (by norm_num : (0:ℝ) ≤ 1) hθ hθ1
  have he (a : ℝ) : 1*d⁻¹*a = a/d := by ring
  rw [he,he,ENNReal.ofReal_one,mul_one] at h
  rw [Real.enorm_eq_ofReal (normalizedPostRate_nonneg hf z),
    Real.enorm_eq_ofReal (normalizedPreRate_nonneg hf z)]
  exact h

omit [SFinite μ] in
theorem normalizedPostRate_integrable {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hpre : Integrable (normalizedPreRate f)
      ((μ.prod volume).prod ((volume : Measure Velocity).prod sphereArea)))
    (hD : (∫⁻ z : (X × Velocity) × (Velocity × Sphere), extendedEntropyProduction
      (postRate f (collisionGrouping.symm z)) (preRate f (collisionGrouping.symm z))
      ∂((μ.prod volume).prod ((volume : Measure Velocity).prod sphereArea))) < ⊤) :
    Integrable (normalizedPostRate f)
      ((μ.prod volume).prod ((volume : Measure Velocity).prod sphereArea)) := by
  let ν : Measure ((X × Velocity) × (Velocity × Sphere)) := (μ.prod volume).prod ((volume : Measure Velocity).prod sphereArea)
  have hpm := (normalizedPreRate_measurable hfm).enorm
  have hdm : Measurable (fun z : (X × Velocity) × (Velocity × Sphere) =>
      extendedEntropyProduction (postRate f (collisionGrouping.symm z)) (preRate f (collisionGrouping.symm z))) := measurable_extendedEntropyProduction
    (((preRate_measurable hfm).comp scatterTriple_measurable).comp collisionGrouping.symm.measurable)
    ((preRate_measurable hfm).comp collisionGrouping.symm.measurable)
  refine ⟨(normalizedPostRate_measurable hfm).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ z, ‖normalizedPostRate f z‖ₑ ∂ν) ≤ ∫⁻ z, 2*‖normalizedPreRate f z‖ₑ+
        ENNReal.ofReal (2/Real.log 2)*extendedEntropyProduction
          (postRate f (collisionGrouping.symm z)) (preRate f (collisionGrouping.symm z)) ∂ν :=
      lintegral_mono (normalizedPostRate_entropy_bound hfn)
    _ = 2*(∫⁻ z, ‖normalizedPreRate f z‖ₑ ∂ν)+
        ENNReal.ofReal (2/Real.log 2)*(∫⁻ z, extendedEntropyProduction
          (postRate f (collisionGrouping.symm z)) (preRate f (collisionGrouping.symm z)) ∂ν) := by
      have hm2 : Measurable (fun z => (2:ℝ≥0∞)*‖normalizedPreRate f z‖ₑ) := measurable_const.mul hpm
      rw [lintegral_add_left hm2,lintegral_const_mul (2:ℝ≥0∞) hpm,
        lintegral_const_mul (ENNReal.ofReal (2/Real.log 2)) hdm]
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num)
      (hasFiniteIntegral_iff_enorm.mp hpre.hasFiniteIntegral),
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD⟩

theorem normalizedPostRate_integral (f : X × Velocity → ℝ) (p : X × Velocity) :
    (∫ q, normalizedPostRate f (p,q) ∂((volume : Measure Velocity).prod sphereArea)) =
      gainDensity f p/(1+f p/maxwellian p.2) := by
  unfold normalizedPostRate gainDensity
  dsimp only
  rw [integral_div]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The renormalized characteristic equation tested along a smooth path -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Renormalization

theorem tested_chain_rule (β : Renormalization) {a b : ℝ} (hab : a ≤ b)
    {F r ψ ψ' : ℝ → ℝ} (hF : AbsolutelyContinuousOnInterval F a b)
    (hFn : ∀ t ∈ Icc a b, 0 ≤ F t)
    (hr : ∀ᵐ t, t ∈ Icc a b → HasDerivAt F (r t) t)
    (hψ : AbsolutelyContinuousOnInterval ψ a b)
    (hψ' : ∀ᵐ t, t ∈ Icc a b → HasDerivAt ψ (ψ' t) t) :
    (∫ t in a..b, derivWithin β.toFun (Ici 0) (F t)*r t*ψ t+β.toFun (F t)*ψ' t) =
      β.toFun (F b)*ψ b-β.toFun (F a)*ψ a := by
  obtain ⟨C,hC⟩ := β.exists_lipschitz
  have hB : AbsolutelyContinuousOnInterval (fun t => β.toFun (F t)) a b :=
    hC.comp_absolutelyContinuousOnInterval
      (fun t ht => hFn t (by simpa only [uIcc_of_le hab] using ht)) hF
  calc
    _ = ∫ t in a..b, deriv (fun s => β.toFun (F s)) t*ψ t+
        β.toFun (F t)*deriv ψ t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hr,hψ',Measure.ae_ne (volume : Measure ℝ) b] with t ht hpt htb htI
      have ht' : t ∈ Ioc a b := by simpa only [uIoc_of_le hab] using htI
      have htcc : t ∈ Icc a b := ⟨ht'.1.le,ht'.2⟩
      have hd := (β.regular.differentiableOn (by norm_num) (F t) (hFn t htcc)).hasDerivWithinAt
      have hc := hd.scomp t (ht htcc).hasDerivWithinAt hFn
      have hda := hc.hasDerivAt (Icc_mem_nhds ht'.1 (lt_of_le_of_ne ht'.2 htb))
      rw [(hpt htcc).deriv]
      have he : deriv (fun s => β.toFun (F s)) t =
          derivWithin β.toFun (Ici 0) (F t)*r t := by
        simpa only [Function.comp_def,smul_eq_mul,mul_comm] using hda.deriv
      rw [he]
    _ = _ := hB.integral_deriv_mul_eq_sub hψ

theorem weighted_tested_chain_rule (β : Renormalization) {a b m : ℝ}
    (hab : a ≤ b) (hm : 0 < m) {F r ψ ψ' : ℝ → ℝ}
    (hF : AbsolutelyContinuousOnInterval F a b)
    (hFn : ∀ t ∈ Icc a b, 0 ≤ F t)
    (hr : ∀ᵐ t, t ∈ Icc a b → HasDerivAt F (r t) t)
    (hψ : AbsolutelyContinuousOnInterval ψ a b)
    (hψ' : ∀ᵐ t, t ∈ Icc a b → HasDerivAt ψ (ψ' t) t) :
    (∫ t in a..b, derivWithin β.toFun (Ici 0) (F t/m)*r t*ψ t+
      m*β.toFun (F t/m)*ψ' t) =
      m*β.toFun (F b/m)*ψ b-m*β.toFun (F a/m)*ψ a := by
  have hF' : AbsolutelyContinuousOnInterval (fun t => F t/m) a b := by
    simpa only [div_eq_mul_inv,mul_comm] using
      AbsolutelyContinuousOnInterval.const_mul m⁻¹ hF
  have hr' : ∀ᵐ t, t ∈ Icc a b → HasDerivAt (fun t => F t/m) (r t/m) t := by
    filter_upwards [hr] with t ht hmem
    exact (ht hmem).div_const m
  have he := congrArg (fun x : ℝ => m*x) (β.tested_chain_rule hab hF'
    (fun t ht => div_nonneg (hFn t ht) hm.le) hr' hψ hψ')
  rw [← intervalIntegral.integral_const_mul] at he
  have hi : (fun t => m*(derivWithin β.toFun (Ici 0) (F t/m)*(r t/m)*ψ t+
      β.toFun (F t/m)*ψ' t)) =
      (fun t => derivWithin β.toFun (Ici 0) (F t/m)*r t*ψ t+
        m*β.toFun (F t/m)*ψ' t) := by
    funext t
    field_simp
  rw [hi] at he
  exact he.trans (by ring)

end BoltzmannNonuniqueness.Renormalization

end

end

section

/-! # Renormalization of a nonnegative integral path -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Renormalization

theorem integral_path_data {a b A : ℝ} {r : ℝ → ℝ} (hab : a ≤ b)
    (hr : IntervalIntegrable r volume a b) :
    AbsolutelyContinuousOnInterval (fun t => A+∫ s in a..t, r s) a b ∧
      (∀ᵐ t, t ∈ Icc a b → HasDerivAt (fun t => A+∫ s in a..t, r s) (r t) t) := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => A) a b := by
    simpa only [AbsolutelyContinuousOnInterval,dist_self,Finset.sum_const_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ × (ℕ → ℝ × ℝ) => (0:ℝ)) _ _)
  refine ⟨hc.add (hr.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc),?_⟩
  filter_upwards [hr.ae_hasDerivAt_integral] with t ht hmem
  exact (ht (by simpa only [uIcc_of_le hab] using hmem) a left_mem_uIcc).const_add A

theorem weighted_integral_path (β : Renormalization) {a b m A : ℝ} {r : ℝ → ℝ}
    (hab : a ≤ b) (hm : 0 < m) (hr : IntervalIntegrable r volume a b)
    (hn : ∀ t ∈ Icc a b, 0 ≤ A+∫ s in a..t, r s) :
    (∫ t in a..b, derivWithin β.toFun (Ici 0) ((A+∫ s in a..t, r s)/m)*r t) =
      m*β.toFun ((A+∫ s in a..b, r s)/m)-m*β.toFun (A/m) := by
  obtain ⟨hp,hd⟩ := integral_path_data hab hr (A := A)
  simpa only [intervalIntegral.integral_same,add_zero] using
    β.weighted_chain_rule hab hm hp hn hd

theorem weighted_tested_integral_path (β : Renormalization)
    {a b m A : ℝ} {r ψ ψ' : ℝ → ℝ} (hab : a ≤ b) (hm : 0 < m)
    (hr : IntervalIntegrable r volume a b)
    (hn : ∀ t ∈ Icc a b, 0 ≤ A+∫ s in a..t, r s)
    (hψ : AbsolutelyContinuousOnInterval ψ a b)
    (hψ' : ∀ᵐ t, t ∈ Icc a b → HasDerivAt ψ (ψ' t) t) :
    (∫ t in a..b, derivWithin β.toFun (Ici 0) ((A+∫ s in a..t, r s)/m)*r t*ψ t+
      m*β.toFun ((A+∫ s in a..t, r s)/m)*ψ' t) =
      m*β.toFun ((A+∫ s in a..b, r s)/m)*ψ b-m*β.toFun (A/m)*ψ a := by
  obtain ⟨hp,hd⟩ := integral_path_data hab hr (A := A)
  simpa only [intervalIntegral.integral_same,add_zero] using
    β.weighted_tested_chain_rule hab hm hp hn hd hψ hψ'

end BoltzmannNonuniqueness.Renormalization

end

end

section

/-! # Exponential localization of a renormalized integral characteristic -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Renormalization

theorem localized_integral_path (β : Renormalization) {t m A : ℝ} {r χ : ℝ → ℝ}
    (ht : 0 ≤ t) (hm : 0 < m) (hr : IntervalIntegrable r volume 0 t)
    (hn : ∀ s ∈ Icc 0 t, 0 ≤ A+∫ u in 0..s, r u) (hχ : ContDiff ℝ 1 χ) :
    χ t*(m*β.toFun ((A+∫ s in 0..t, r s)/m)) =
      Real.exp (-t)*χ 0*(m*β.toFun (A/m))+
      ∫ s in 0..t, Real.exp (-(t-s))*(χ s*(derivWithin β.toFun (Ici 0)
        ((A+∫ u in 0..s, r u)/m)*r s)+
        (deriv χ s+χ s)*(m*β.toFun ((A+∫ u in 0..s, r u)/m))) := by
  let ψ : ℝ → ℝ := fun s => Real.exp (s-t)*χ s
  let ψ' : ℝ → ℝ := fun s => Real.exp (s-t)*(deriv χ s+χ s)
  have hp : ContDiff ℝ 1 ψ := by
    apply ContDiff.mul _ hχ
    exact Real.contDiff_exp.comp (contDiff_id.sub contDiff_const)
  have hd : ∀ s, HasDerivAt ψ (ψ' s) s := by
    intro s
    have he : HasDerivAt (fun u : ℝ => Real.exp (u-t)) (Real.exp (s-t)) s := by
      simpa only [id_eq,mul_one] using ((hasDerivAt_id s).sub_const t).exp
    convert he.mul (hχ.differentiable (by norm_num) s).hasDerivAt using 1
    dsimp only [ψ,ψ']
    ring
  have h := β.weighted_tested_integral_path ht hm hr hn
    hp.contDiffOn.absolutelyContinuousOnInterval
    (ae_of_all _ (fun s _ => hd s))
  have hleft : (∫ s in 0..t, derivWithin β.toFun (Ici 0)
      ((A+∫ u in 0..s, r u)/m)*r s*ψ s+
      m*β.toFun ((A+∫ u in 0..s, r u)/m)*ψ' s) =
    ∫ s in 0..t, Real.exp (-(t-s))*(χ s*(derivWithin β.toFun (Ici 0)
      ((A+∫ u in 0..s, r u)/m)*r s)+
      (deriv χ s+χ s)*(m*β.toFun ((A+∫ u in 0..s, r u)/m))) := by
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only [ψ,ψ']
    rw [show s-t = -(t-s) by ring]
    ring
  rw [hleft] at h
  dsimp only [ψ] at h
  simp only [sub_self,Real.exp_zero,one_mul,zero_sub] at h
  linarith

end BoltzmannNonuniqueness.Renormalization

end

end

section

/-! # Renormalization of a source integrable after division by one plus density -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Renormalization
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem derivative_comp_aestronglyMeasurable (β : Renormalization) {f : X → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hfn : ∀ᵐ x ∂μ, 0 ≤ f x) :
    AEStronglyMeasurable (fun x => derivWithin β.toFun (Ici 0) (f x)) μ := by
  let g x := max 0 (hfm.mk f x)
  have hgm : Measurable g := measurable_const.max hfm.stronglyMeasurable_mk.measurable
  have he : g =ᵐ[μ] f := by
    filter_upwards [hfn,hfm.ae_eq_mk] with x hn hx
    change max 0 (hfm.mk f x) = f x
    rw [← hx,max_eq_right hn]
  exact (β.measurable_derivative_comp hgm (fun x => le_max_left _ _)).aestronglyMeasurable.congr
    (he.mono (fun x hx => congrArg (fun u => derivWithin β.toFun (Ici 0) u) hx))

theorem derivative_mul_integrable_of_normalized (β : Renormalization) {f r : X → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hfn : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hri : Integrable (fun x => r x/(1+f x)) μ) :
    Integrable (fun x => derivWithin β.toFun (Ici 0) (f x)*r x) μ := by
  obtain ⟨C,hC,hb⟩ := β.derivative_bound
  have hm : AEStronglyMeasurable (fun x => derivWithin β.toFun (Ici 0) (f x)*(1+f x)) μ := (β.derivative_comp_aestronglyMeasurable hfm hfn).mul
    (aestronglyMeasurable_const.add hfm)
  have hh : ∀ᵐ x ∂μ, |derivWithin β.toFun (Ici 0) (f x)*(1+f x)| ≤ C := by
    filter_upwards [hfn] with x hx
    rw [abs_mul,abs_of_pos (by positivity : 0 < 1+f x)]
    exact (mul_le_mul_of_nonneg_right (hb (f x) hx) (by positivity)).trans_eq
      (div_mul_cancel₀ C (by positivity))
  have hi := hri.bdd_mul hm hh
  apply hi.congr
  filter_upwards [hfn] with x hx
  change (derivWithin β.toFun (Ici 0) (f x)*(1+f x))*(r x/(1+f x)) = _
  field_simp

end BoltzmannNonuniqueness.Renormalization

end

end

section

/-! # Integrability of the tested renormalized time traces -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.KineticTest

theorem weighted_slice_integrable (φ : KineticTest) (β : Renormalization)
    {T t : ℝ} (ht : t ∈ Icc 0 T) {f : Density}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p) (hfi : Integrable f) :
    Integrable (fun p => maxwellian p.2*β.toFun (f p/maxwellian p.2)*φ.toFun t p.1 p.2) := by
  have hmm : Measurable (fun p : Phase => maxwellian p.2) := by
    unfold maxwellian
    fun_prop
  have hi := β.weighted_integrable hfm hmm hfn (fun p => maxwellian_pos p.2) hfi
  have hφ : Measurable (fun p : Phase => φ.toFun t p.1 p.2) :=
    φ.measurable_toFun.comp (measurable_const.prodMk measurable_id)
  obtain ⟨C,_hC,hb⟩ := φ.bounded_on_time T
  apply hi.mul_bdd hφ.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    simpa only [Real.norm_eq_abs] using (hb t ht p).1)

end BoltzmannNonuniqueness.KineticTest

end

end

section

/-! # Weighted renormalizations of almost-everywhere nonnegative L1 fields -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Renormalization
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem weighted_integrable_of_ae (β : Renormalization) {f m : X → ℝ}
    (hmm : Measurable m) (hm : ∀ x, 0 < m x)
    (hfn : ∀ᵐ x ∂μ, 0 ≤ f x) (hfi : Integrable f μ) :
    Integrable (fun x => m x*β.toFun (f x/m x)) μ := by
  let g x := max 0 (hfi.aestronglyMeasurable.mk f x)
  have hgm : Measurable g := measurable_const.max hfi.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have he : g =ᵐ[μ] f := by
    filter_upwards [hfn,hfi.aestronglyMeasurable.ae_eq_mk] with x hn hx
    change max 0 (hfi.aestronglyMeasurable.mk f x) = f x
    rw [← hx,max_eq_right hn]
  have hgi : Integrable g μ := hfi.congr he.symm
  exact (β.weighted_integrable hgm hmm (fun x => le_max_left _ _) hm hgi).congr
    (he.mono (fun x hx => congrArg (fun u => m x*β.toFun (u/m x)) hx))

end BoltzmannNonuniqueness.Renormalization

end

end

end OAI
