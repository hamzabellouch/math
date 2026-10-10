import OAI.MathematicalPhysics.Boltzmann.Admissibility
import OAI.MathematicalPhysics.Boltzmann.Branching.AttenuationGap
import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedAverageProducts
import OAI.MathematicalPhysics.Boltzmann.Branching.RealL1ApproximationLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.TimeSourceCumulative
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedHotRegularity
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedPairUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityCutoffEntropyError
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedPairCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairPatchIdentity
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongMassClip
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakEntropyMarginal
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

namespace OAI

section

/-! # Strong L1 continuity of the time primitive on a finite time window -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Published
open Compactness
variable {P : Type*} [MeasurableSpace P]
variable {μ : Measure ℝ} {ν : Measure P} [IsFiniteMeasure μ] [SFinite ν]

theorem strong_timePrimitive {f : ℕ → ℝ × P → ℝ} {g : ℝ × P → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hfi : ∀ n, Integrable (f n) (μ.prod ν)) (hgi : Integrable g (μ.prod ν))
    (ht : Tendsto (fun n => eLpNorm (f n-g) 1 (μ.prod ν)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (timePrimitive μ (f n)-timePrimitive μ g) 1 (μ.prod ν))
      atTop (𝓝 0) := by
  let F n (z : (ℝ × P) × ℝ) := f n (z.2,z.1.2)
  let G (z : (ℝ × P) × ℝ) := g (z.2,z.1.2)
  have hFm n : Measurable (F n) := (hfm n).comp (measurable_snd.prodMk measurable_fst.snd)
  have hGm : Measurable G := hgm.comp (measurable_snd.prodMk measurable_fst.snd)
  have hFi n : Integrable (F n) ((μ.prod ν).prod μ) :=
    (timeExchange_measurePreserving μ ν).integrable_comp_of_integrable ((hfi n).comp_fst μ)
  have hGi : Integrable G ((μ.prod ν).prod μ) :=
    (timeExchange_measurePreserving μ ν).integrable_comp_of_integrable (hgi.comp_fst μ)
  have hlift := strongL1_comp_fst (ν := μ) (fun n => (hfm n).sub hgm) ht
  have hex n : eLpNorm (F n-G) 1 ((μ.prod ν).prod μ) =
      eLpNorm (fun z : (ℝ × P) × ℝ => (f n-g) z.1) 1 ((μ.prod ν).prod μ) :=
    eLpNorm_comp_measurePreserving
      (((hfm n).sub hgm).comp measurable_fst).aestronglyMeasurable
      (timeExchange_measurePreserving μ ν)
  have ht' : Tendsto (fun n => eLpNorm (F n-G) 1 ((μ.prod ν).prod μ)) atTop (𝓝 0) := by
    simpa only [hex] using hlift
  let k (z : (ℝ × P) × ℝ) : ℝ := if z.2 ≤ z.1.1 then 1 else 0
  have hkm : Measurable k := measurable_const.ite
    (measurableSet_le measurable_snd measurable_fst.fst) measurable_const
  have hkb z : |k z| ≤ 1 := by dsimp only [k]; split <;> norm_num
  have he (u : ℝ × P → ℝ) z : (∫ s, k (z,s)*u (s,z.2) ∂μ) = timePrimitive μ u z := by
    apply integral_congr_ae
    apply ae_of_all
    intro s
    dsimp only [k,timePrimitive]
    split <;> simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht' (fun _ => zero_le)
  intro n
  have h := weighted_average_difference_le (hFm n) hGm hkm (hFi n) hGi hkb
  change eLpNorm (fun z => timePrimitive μ (f n) z-timePrimitive μ g z) 1 (μ.prod ν) ≤ _
  simpa only [F,G,he,ENNReal.ofReal_one,one_mul] using h

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Restriction of the common strong initial interval -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness

theorem StrongEarly.restrict {T U : ℝ} {F : Evolution} (S : StrongEarly U F)
    (hT : 0 < T) (hTU : T ≤ U) : StrongEarly T F := by
  have hs : Icc (0:ℝ) T ⊆ Icc 0 U := Icc_subset_Icc le_rfl hTU
  have hp : boundedTimes T ⊆ boundedTimes U := Set.prod_mono hs (Subset.refl _)
  exact ⟨hT,fun t ht => (S.strong_continuity t (hs ht)).mono_left (nhdsWithin_mono t hs),
    S.gain_integrable.mono_set hp,S.loss_integrable.mono_set hp⟩

end BoltzmannNonuniqueness

end

end

section

/-! # Strong L¹ limits preserve the entropy bound at every time -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem weakL1_of_eLpNorm_sub {f : ℕ → X → ℝ} {g : X → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hgm : Measurable g) (hg : Integrable g μ)
    (ht : Tendsto (fun n => eLpNorm (fun x => f n x-g x) 1 μ) atTop (𝓝 0)) :
    WeakL1Converges μ f g := by
  apply weakL1_of_integral_norm_sub hf hgm hg
  have he n : (∫ x, ‖f n x-g x‖ ∂μ) =
      (eLpNorm (fun x => f n x-g x) 1 μ).toReal := by
    change (∫ x, ‖(f n-g) x‖ ∂μ) = (eLpNorm (f n-g) 1 μ).toReal
    rw [eLpNorm_one_eq_lintegral_enorm ((hf n).sub hg).aestronglyMeasurable,
      integral_norm_eq_lintegral_enorm ((hf n).sub hg).aestronglyMeasurable]
  simp only [he]
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht

theorem entropy_liminf_of_eLpNorm_sub {f : ℕ → X → ℝ} {g m : X → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hgm : Measurable g) (hg : Integrable g μ)
    (ht : Tendsto (fun n => eLpNorm (fun x => f n x-g x) 1 μ) atTop (𝓝 0))
    (hfn : ∀ n, 0 ≤ᵐ[μ] f n) (hgn : 0 ≤ᵐ[μ] g)
    (hmm : Measurable m) (hmi : Integrable m μ) (hmp : ∀ᵐ x ∂μ, 0 < m x) :
    (∫⁻ x, ENNReal.ofReal (scalarRelativeEntropy (m x) (g x)) ∂μ) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (scalarRelativeEntropy (m x) (f n x)) ∂μ) atTop :=
  (weakL1_of_eLpNorm_sub hf hgm hg ht).entropy_liminf hf hfn hgn hmm hmi hmp

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Strong stability of positive survival factors from L1 convergence of the rates -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Published
variable {P : Type*} [MeasurableSpace P]
variable {μ : Measure ℝ} {ν : Measure P} [IsFiniteMeasure μ] [SFinite ν]

def timeSurvival (μ : Measure ℝ) (f : ℝ × P → ℝ) (z : ℝ × P) : ℝ :=
  Real.exp (-timePrimitive μ f z)

theorem timeSurvival_measurable {f : ℝ × P → ℝ} (hf : Measurable f) :
    Measurable (timeSurvival μ f) := (timePrimitive_measurable μ hf).neg.exp

omit [MeasurableSpace P] [IsFiniteMeasure μ] [SFinite ν] in
theorem timePrimitive_nonneg {f : ℝ × P → ℝ} (hf : ∀ z, 0 ≤ f z) (z : ℝ × P) :
    0 ≤ timePrimitive μ f z := by
  apply integral_nonneg
  intro s
  dsimp only [timePrimitive]
  split
  · exact hf (s,z.2)
  · exact le_rfl

omit [MeasurableSpace P] [IsFiniteMeasure μ] [SFinite ν] in
theorem timeSurvival_bounds {f : ℝ × P → ℝ} (hf : ∀ z, 0 ≤ f z) (z : ℝ × P) :
    0 < timeSurvival μ f z ∧ timeSurvival μ f z ≤ 1 :=
  ⟨Real.exp_pos _,Real.exp_le_one_iff.mpr (neg_nonpos.mpr (timePrimitive_nonneg hf z))⟩

theorem strong_timeSurvival {f : ℕ → ℝ × P → ℝ} {g : ℝ × P → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hfi : ∀ n, Integrable (f n) (μ.prod ν)) (hgi : Integrable g (μ.prod ν))
    (hfn : ∀ n z, 0 ≤ f n z) (hgn : ∀ z, 0 ≤ g z)
    (ht : Tendsto (fun n => eLpNorm (f n-g) 1 (μ.prod ν)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (timeSurvival μ (f n)-timeSurvival μ g) 1 (μ.prod ν))
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (strong_timePrimitive hfm hgm hfi hgi ht) (fun _ => zero_le)
  intro n
  apply eLpNorm_mono ((timeSurvival_measurable (hfm n)).sub (timeSurvival_measurable hgm)).aestronglyMeasurable
  intro z
  simpa only [Pi.sub_apply,Real.norm_eq_abs,timeSurvival] using
    AttenuationLipschitz.exp_neg_difference (timePrimitive_nonneg (hfn n) z)
      (timePrimitive_nonneg hgn z)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Strong L1 convergence with uniformly small errors on both sides -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem strongL1_of_two_sided_approximations
    {f : ℕ → X → ℝ} {g : X → ℝ} {u : ℕ → ℕ → X → ℝ} {v : ℕ → X → ℝ}
    {δ : ℕ → ℝ≥0∞} (hδ : Tendsto δ atTop (𝓝 0))
    (hf : ∀ j n, eLpNorm (f n-u j n) 1 μ ≤ δ j)
    (hg : ∀ j, eLpNorm (v j-g) 1 μ ≤ δ j)
    (hu : ∀ j, Tendsto (fun n => eLpNorm (u j n-v j) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n-g) 1 μ) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hε4 : 0 < ε/4 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨j,hj⟩ := (ENNReal.tendsto_nhds_zero.mp hδ (ε/4) hε4).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hu j) (ε/4) hε4] with n hn
  have htri (a b c : X → ℝ) : eLpNorm (a-c) 1 μ ≤ eLpNorm (a-b) 1 μ+eLpNorm (b-c) 1 μ := by
    have he : a-c = (a-b)+(b-c) := by ext x; simp
    rw [he]
    exact eLpNorm_add_le (by norm_num)
  calc
    _ ≤ eLpNorm (f n-u j n) 1 μ+eLpNorm (u j n-g) 1 μ := htri _ _ _
    _ ≤ δ j+(eLpNorm (u j n-v j) 1 μ+δ j) :=
      add_le_add (hf j n) ((htri _ _ _).trans (add_le_add le_rfl (hg j)))
    _ ≤ ε/4+(ε/4+ε/4) := add_le_add hj (add_le_add hn hj)
    _ ≤ ε := by
      calc
        ε/4+(ε/4+ε/4) ≤ ε/4+(ε/4+(ε/4+ε/4)) := by gcongr; exact le_self_add
        _ = 4*(ε/4) := by ring
        _ = ε := ENNReal.mul_div_cancel (by norm_num) (by norm_num)

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Strong convergence of physical survival kernels with two time endpoints -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Published
open Compactness
variable {P : Type*} [MeasurableSpace P]
variable {μ : Measure ℝ} {ν : Measure P} [IsFiniteMeasure μ] [SFinite ν]

def timeDifference (u : ℝ × P → ℝ) (z : (ℝ × P) × ℝ) : ℝ := u z.1-u (z.2,z.1.2)

theorem timeDifference_measurable {u : ℝ × P → ℝ} (hu : Measurable u) :
    Measurable (timeDifference u) :=
  (hu.comp measurable_fst).sub (hu.comp (measurable_snd.prodMk measurable_fst.snd))

theorem strong_timeDifference {u : ℕ → ℝ × P → ℝ} {v : ℝ × P → ℝ}
    (hum : ∀ n, Measurable (u n)) (hvm : Measurable v)
    (ht : Tendsto (fun n => eLpNorm (u n-v) 1 (μ.prod ν)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (timeDifference (u n)-timeDifference v) 1 ((μ.prod ν).prod μ))
      atTop (𝓝 0) := by
  have hfirst := strongL1_comp_fst (ν := μ) (fun n => (hum n).sub hvm) ht
  have hsecond : Tendsto (fun n => eLpNorm
      (fun z : (ℝ × P) × ℝ => u n (z.2,z.1.2)-v (z.2,z.1.2)) 1 ((μ.prod ν).prod μ))
      atTop (𝓝 0) := by
    have he n : eLpNorm (fun z : (ℝ × P) × ℝ => u n (z.2,z.1.2)-v (z.2,z.1.2))
        1 ((μ.prod ν).prod μ) = eLpNorm (fun z : (ℝ × P) × ℝ => (u n-v) z.1)
        1 ((μ.prod ν).prod μ) :=
      eLpNorm_comp_measurePreserving (((hum n).sub hvm).comp measurable_fst).aestronglyMeasurable
        (timeExchange_measurePreserving μ ν)
    simpa only [he] using hfirst
  have hs := hfirst.add hsecond
  simp only [zero_add] at hs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => zero_le)
  intro n
  change eLpNorm (timeDifference (u n)-timeDifference v) 1 ((μ.prod ν).prod μ) ≤
    eLpNorm (fun z : (ℝ × P) × ℝ => (u n-v) z.1) 1 ((μ.prod ν).prod μ)+
      eLpNorm (fun z : (ℝ × P) × ℝ => u n (z.2,z.1.2)-v (z.2,z.1.2))
        1 ((μ.prod ν).prod μ)
  have he : timeDifference (u n)-timeDifference v =
      (fun z : (ℝ × P) × ℝ => (u n-v) z.1)-
      (fun z : (ℝ × P) × ℝ => u n (z.2,z.1.2)-v (z.2,z.1.2)) := by
    funext z
    dsimp only [timeDifference,Pi.sub_apply]
    ring
  rw [he]
  exact eLpNorm_sub_le (by norm_num)

def twoTimeSurvival (μ : Measure ℝ) (f : ℝ × P → ℝ) (z : (ℝ × P) × ℝ) : ℝ :=
  Real.exp (-max 0 (timeDifference (timePrimitive μ f) z))

omit [MeasurableSpace P] [IsFiniteMeasure μ] [SFinite ν] in
theorem twoTimeSurvival_bounds (μ : Measure ℝ) (f : ℝ × P → ℝ) (z : (ℝ × P) × ℝ) :
    0 < twoTimeSurvival μ f z ∧ twoTimeSurvival μ f z ≤ 1 :=
  ⟨Real.exp_pos _,Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_left 0 _))⟩

theorem twoTimeSurvival_measurable {f : ℝ × P → ℝ} (hf : Measurable f) :
    Measurable (twoTimeSurvival μ f) :=
  (measurable_const.max (timeDifference_measurable (timePrimitive_measurable μ hf))).neg.exp

theorem strong_twoTimeSurvival {f : ℕ → ℝ × P → ℝ} {g : ℝ × P → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hfi : ∀ n, Integrable (f n) (μ.prod ν)) (hgi : Integrable g (μ.prod ν))
    (ht : Tendsto (fun n => eLpNorm (f n-g) 1 (μ.prod ν)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (twoTimeSurvival μ (f n)-twoTimeSurvival μ g)
      1 ((μ.prod ν).prod μ)) atTop (𝓝 0) := by
  have h := strong_timeDifference (fun n => timePrimitive_measurable μ (hfm n))
    (timePrimitive_measurable μ hgm) (strong_timePrimitive hfm hgm hfi hgi ht)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
  intro n
  apply eLpNorm_mono ((twoTimeSurvival_measurable (hfm n)).sub
    (twoTimeSurvival_measurable hgm)).aestronglyMeasurable
  intro z
  have he := AttenuationLipschitz.exp_neg_difference
    (le_max_left 0 (timeDifference (timePrimitive μ (f n)) z))
    (le_max_left 0 (timeDifference (timePrimitive μ g) z))
  have hm := abs_max_sub_max_le_max 0 (timeDifference (timePrimitive μ (f n)) z)
    0 (timeDifference (timePrimitive μ g) z)
  have hmax : max (0:ℝ)
      |timeDifference (timePrimitive μ (f n)) z-timeDifference (timePrimitive μ g) z| =
      |timeDifference (timePrimitive μ (f n)) z-timeDifference (timePrimitive μ g) z| :=
    max_eq_right (abs_nonneg _)
  simpa only [Pi.sub_apply,twoTimeSurvival,Real.norm_eq_abs,sub_self,abs_zero,
    hmax] using he.trans hm

omit [MeasurableSpace P] [IsFiniteMeasure μ] [SFinite ν] in
theorem twoTimeSurvival_eq_interval {T s t : ℝ} (ht : t ∈ Set.Icc 0 T)
    (hs : s ∈ Set.Icc 0 t) {f : ℝ × P → ℝ} (hf : ∀ z, 0 ≤ f z) (p : P)
    (hi : IntervalIntegrable (fun r => f (r,p)) volume 0 T) :
    twoTimeSurvival (volume.restrict (Set.Icc 0 T)) f ((t,p),s) =
      Real.exp (-(∫ r in s..t, f (r,p))) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0s : IntervalIntegrable (fun r => f (r,p)) volume 0 s := by
    apply hi.mono_set
    rw [Set.uIcc_of_le hs.1,Set.uIcc_of_le hT]
    intro r hr
    exact ⟨hr.1,hr.2.trans (hs.2.trans ht.2)⟩
  have hst : IntervalIntegrable (fun r => f (r,p)) volume s t := by
    apply hi.mono_set
    rw [Set.uIcc_of_le hs.2,Set.uIcc_of_le hT]
    intro r hr
    exact ⟨hs.1.trans hr.1,hr.2.trans ht.2⟩
  have he := intervalIntegral.integral_add_adjacent_intervals h0s hst
  have hd : (∫ r in 0..t, f (r,p))-(∫ r in 0..s, f (r,p)) = ∫ r in s..t, f (r,p) := by
    linarith
  have hn : 0 ≤ ∫ r in s..t, f (r,p) :=
    intervalIntegral.integral_nonneg hs.2 (fun r _ => hf (r,p))
  simp only [twoTimeSurvival,timeDifference,timePrimitive_eq_interval ht,
    timePrimitive_eq_interval (show s ∈ Set.Icc 0 T from ⟨hs.1,hs.2.trans ht.2⟩),hd,max_eq_right hn]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Strong velocity averages retain the first moment under a common entropy bound -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness
open PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem strong_linearMoment_averages
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hfi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hfb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hgm : Measurable g) (hg : ∀ p, 0 ≤ g p)
    (hgi : Integrable (entropyGauge g) (μ.prod volume))
    (hgb : (∫ p, entropyGauge g p ∂μ.prod volume) ≤ C)
    (ha : ∀ (ψ : Velocity → ℝ), Measurable ψ → ∀ D : ℝ≥0, (∀ v, |ψ v| ≤ D) →
      Tendsto (fun n => eLpNorm (fun x => (∫ v, ψ v*f n (x,v))-
        (∫ v, ψ v*g (x,v))) 1 μ) atTop (𝓝 0))
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) (D : ℝ≥0) (hD : ∀ v, |ψ v| ≤ D) :
    Tendsto (fun n => eLpNorm (fun x => (∫ v, ψ v*linearMoment (f n) (x,v))-
      (∫ v, ψ v*linearMoment g (x,v))) 1 μ) atTop (𝓝 0) := by
  let R : ℕ → ℝ := fun j => (j:ℝ)+1
  have hR j : 0 < R j := by dsimp [R]; positivity
  let b : ℕ → Velocity → ℝ := fun j v => if ‖v‖ ≤ R j then ψ v*(1+‖v‖) else 0
  have hbm j : Measurable (b j) := (hψ.mul (measurable_const.add measurable_id.norm)).ite
    (measurableSet_le measurable_id.norm measurable_const) measurable_const
  have hb j v : |b j v| ≤ (D:ℝ)*(1+R j) := by
    dsimp only [b]
    split_ifs with hv
    · rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1+‖v‖)]
      exact mul_le_mul (hD v) (by linarith) (by positivity) D.coe_nonneg
    · simp only [abs_zero]
      positivity
  let A (u : X × Velocity → ℝ) x := ∫ v, ψ v*linearMoment u (x,v)
  let U j (u : X × Velocity → ℝ) x := ∫ v, ψ v*velocityLinearCut (R j) u (x,v)
  have he j (u : X × Velocity → ℝ) x : U j u x = ∫ v, b j v*u (x,v) := by
    apply integral_congr_ae
    apply ae_of_all
    intro v
    dsimp only [b,U,velocityLinearCut,linearMoment]
    split_ifs <;> ring
  have hc j : Tendsto (fun n => eLpNorm (U j (f n)-U j g) 1 μ) atTop (𝓝 0) := by
    change Tendsto (fun n => eLpNorm (fun x => U j (f n) x-U j g x) 1 μ) atTop (𝓝 0)
    simp_rw [he]
    exact ha (b j) (hbm j) ⟨(D:ℝ)*(1+R j),by positivity⟩ (hb j)
  have herr (u : X × Velocity → ℝ) (hum : Measurable u) (hun : ∀ p, 0 ≤ u p)
      (hui : Integrable (entropyGauge u) (μ.prod volume))
      (hub : (∫ p, entropyGauge u p ∂μ.prod volume) ≤ C) j :
      eLpNorm (A u-U j u) 1 μ ≤ ENNReal.ofReal ((D:ℝ)*(2*C/R j)) := by
    apply (weighted_average_difference_le (linearMoment_measurable hum)
      (velocityLinearCut_measurable (R j) hum) (hψ.comp measurable_snd)
      (linearMoment_integrable hum hun hui) (velocityLinearCut_integrable (R j) hum hun hui)
      (fun p => hD p.2)).trans
    rw [ENNReal.ofReal_mul D.coe_nonneg]
    exact mul_le_mul' le_rfl (velocityLinearCut_L1_error (hR j) hum hun hui hub)
  have hδ : Tendsto (fun j => ENNReal.ofReal ((D:ℝ)*(2*C/R j))) atTop (𝓝 0) := by
    have ht : Tendsto (fun j => 2*C/R j) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa only [Function.comp_def,mul_zero,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (ht.const_mul (D:ℝ))
  exact strongL1_of_two_sided_approximations hδ
    (fun j n => herr (f n) (hfm n) (hf n) (hfi n) (hfb n) j)
    (fun j => by rw [eLpNorm_sub_comm]; exact herr g hgm hg hgi hgb j) hc

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Matched mass-normalized second moments give strong scalar averages -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem strong_of_normalized_second_moments
    {a r : ℕ → X → ℝ} {A R : X → ℝ}
    (ha : Published.WeakL1Converges μ a A) (hr : Published.WeakL1Converges μ r R)
    (hai : ∀ n, Integrable (a n) μ) (hri : ∀ n, Integrable (r n) μ)
    (hrp : ∀ n x, 0 < r n x) (hRp : ∀ x, 0 < R x)
    {B : ℝ} (hB : 0 < B) (hbound : ∀ n, (∫ x, r n x ∂μ) ≤ B)
    (hsi : ∀ n, Integrable (fun x => (a n x)^2/r n x) μ)
    (C : ℝ≥0) (hA : ∀ᵐ x ∂μ, |A x| ≤ C*R x)
    (hsecond : Tendsto (fun n => ∫ x, (a n x)^2/r n x ∂μ)
      atTop (𝓝 (∫ x, (A x)^2/R x ∂μ)))
    (hstrong : Tendsto (fun n => eLpNorm (fun x => r n x-R x) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => a n x-A x) 1 μ) atTop (𝓝 0) := by
  let b := boundedQuotient C A R
  have hbm : Measurable b := boundedQuotient_measurable C ha.1 hr.1
  have hb x : |b x| ≤ C := boundedQuotient_bound C A R x
  have hAe : A =ᵐ[μ] fun x => R x*b x := boundedQuotient_eq_ae C hRp hA
  have he : (∫ x, (A x)^2/R x ∂μ) = ∫ x, (b x*b x)*R x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hAe] with x hx
    rw [hx]
    field_simp [(hRp x).ne']
  rw [he] at hsecond
  exact weighted_moments_strong ha hr hai hri hrp hB hbound hsi hbm C hb hAe hsecond hstrong

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Finite linear operations preserve strong L1 convergence -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem strongL1_add {f g : ℕ → X → ℝ} {F G : X → ℝ}
    (hf : Tendsto (fun n => eLpNorm (fun x => f n x-F x) 1 μ) atTop (𝓝 0))
    (hg : Tendsto (fun n => eLpNorm (fun x => g n x-G x) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => (f n x+g n x)-(F x+G x)) 1 μ) atTop (𝓝 0) := by
  have ht := hf.add hg
  simp only [zero_add] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  have he : (fun x => (f n x+g n x)-(F x+G x)) =
      (fun x => f n x-F x)+(fun x => g n x-G x) := by ext x; simp; ring
  change eLpNorm (fun x => (f n x+g n x)-(F x+G x)) 1 μ ≤ _
  rw [he]
  exact eLpNorm_add_le (by norm_num)

theorem strongL1_const_mul {f : ℕ → X → ℝ} {F : X → ℝ}
    (hf : Tendsto (fun n => eLpNorm (fun x => f n x-F x) 1 μ) atTop (𝓝 0)) (c : ℝ) :
    Tendsto (fun n => eLpNorm (fun x => c*f n x-c*F x) 1 μ) atTop (𝓝 0) := by
  have he n : (fun x => c*f n x-c*F x) = c • (fun x => f n x-F x) := by
    ext x
    simp only [Pi.smul_apply,smul_eq_mul,mul_sub]
  simp_rw [he,eLpNorm_const_smul]
  convert ENNReal.Tendsto.const_mul (a := ‖c‖ₑ) hf (Or.inr (by simp)) using 1
  simp

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Product-test convergence extends to every finite supported tensor sum -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem strong_supported_tensor_pair_tests
    {P : ℕ → X × (Velocity × Velocity) → ℝ} {Q : X × (Velocity × Velocity) → ℝ}
    (hPi : ∀ n, Integrable (P n) (μ.prod volume)) (hQi : Integrable Q (μ.prod volume))
    (hprod : ∀ (a b : C(Velocity,ℝ)), HasCompactSupport a → HasCompactSupport b →
      Tendsto (fun n => eLpNorm (fun x =>
        pairTestAverage (tensorTest a b) (P n) x-pairTestAverage (tensorTest a b) Q x) 1 μ)
        atTop (𝓝 0))
    {k : C(Velocity × Velocity,ℝ)} (hk : IsSupportedTensorSum k) :
    Tendsto (fun n => eLpNorm (fun x => pairTestAverage k (P n) x-pairTestAverage k Q x) 1 μ)
      atTop (𝓝 0) := by
  induction hk with
  | zero => simp [pairTestAverage]
  | tensor a b ha hb => exact hprod a b ha hb
  | @add k l hk hl ihk ihl =>
    have h := strongL1_add ihk ihl
    apply h.congr'
    apply Filter.Eventually.of_forall
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [pairTestAverage_add (hPi n) hk.hasCompactSupport hl.hasCompactSupport,
      pairTestAverage_add hQi hk.hasCompactSupport hl.hasCompactSupport] with x hx hy
    rw [hx,hy]
  | @smul c k hk ih =>
    simpa only [pairTestAverage_smul] using strongL1_const_mul ih c

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Identified normalized pairs force strong convergence of bounded velocity averages -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SFinite ν]

theorem strong_average_of_normalized_pairs
    {f : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (hw : Published.WeakL1Converges (μ.prod ν) f g)
    (hp : Published.WeakL1Converges (μ.prod (ν.prod ν))
      (fun n => normalizedPair ν (f n)) (normalizedPair ν g))
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p) (hg : ∀ p, 0 ≤ g p)
    (hfi : ∀ n, Integrable (f n) (μ.prod ν))
    (hm : Tendsto (fun n => eLpNorm (fun x => fiberMass ν (f n) x-fiberMass ν g x) 1 μ)
      atTop (𝓝 0))
    {B : ℝ} (hB : 0 < B) (hbound : ∀ n, (∫ x, 1+fiberMass ν (f n) x ∂μ) ≤ B)
    {ψ : Y → ℝ} (hψ : Measurable ψ) (C : ℝ≥0) (hC : ∀ y, |ψ y| ≤ C) :
    Tendsto (fun n => eLpNorm (fun x =>
      (∫ v, ψ v*f n (x,v) ∂ν)-(∫ v, ψ v*g (x,v) ∂ν)) 1 μ) atTop (𝓝 0) := by
  let a n x := ∫ v, ψ v*f n (x,v) ∂ν
  let A x := ∫ v, ψ v*g (x,v) ∂ν
  let r n x := 1+fiberMass ν (f n) x
  let R x := 1+fiberMass ν g x
  have hrp n x : 0 < r n x := by
    have h : 0 ≤ fiberMass ν (f n) x := integral_nonneg (fun v => hf n (x,v))
    dsimp only [r]
    linarith
  have hRp x : 0 < R x := by
    have h : 0 ≤ fiberMass ν g x := integral_nonneg (fun v => hg (x,v))
    dsimp only [R]
    linarith
  have ha : Published.WeakL1Converges μ a A :=
    hw.marginal hfi (hψ.comp measurable_snd) C (fun z => hC z.2)
  have hai n : Integrable (a n) μ :=
    ((hfi n).bdd_mul (hψ.comp measurable_snd).aestronglyMeasurable
      (ae_of_all _ (fun z => hC z.2))).integral_prod_left
  have hri n : Integrable (r n) μ := (integrable_const 1).add (hfi n).integral_prod_left
  have hRi : Integrable R μ := (integrable_const 1).add hw.2.1.integral_prod_left
  have hRm : Measurable R := measurable_const.add (fiberMass_measurable hw.1)
  have hrc : Published.WeakL1Converges μ (fun _ : ℕ => R) R :=
    ⟨hRm,hRi,fun _ _ _ => tendsto_const_nhds⟩
  have hstrong : Tendsto (fun n => eLpNorm (fun x => r n x-R x) 1 μ) atTop (𝓝 0) := by
    simpa only [r,R,add_sub_add_left_eq_sub] using hm
  have hr := hrc.of_eLpNorm_sub (fun _ => hRi) hri hstrong
  have hsi n : Integrable (fun x => (a n x)^2/r n x) μ :=
    normalized_average_square_integrable (hfm n) (hf n) (hfi n) hψ hC
  have hs := (weak_normalized_average_squares hfm hf hfi hp hψ hC).2.2
    (fun _ => 1) measurable_const ⟨1,fun _ => by norm_num⟩
  simp only [one_mul] at hs
  have hAb : ∀ᵐ x ∂μ, |A x| ≤ C*R x := by
    filter_upwards [hw.2.1.prod_right_ae] with x hx
    have he := norm_integral_le_of_norm_le (hx.const_mul (C:ℝ))
      (ae_of_all ν (fun v => show ‖ψ v*g (x,v)‖ ≤ C*g (x,v) from by
        rw [norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg (hg (x,v))]
        exact mul_le_mul_of_nonneg_right (hC v) (hg (x,v))))
    have hb : |A x| ≤ C*fiberMass ν g x := by
      simpa only [A,Real.norm_eq_abs,integral_const_mul,fiberMass] using he
    exact hb.trans (by dsimp only [R]; nlinarith [C.coe_nonneg])
  exact strong_of_normalized_second_moments ha hr hai hri hrp hRp hB hbound hsi C hAb hs hstrong

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Strong convergence against every continuous compact velocity-pair test -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem strong_compact_pair_tests
    {P : ℕ → X × (Velocity × Velocity) → ℝ} {Q : X × (Velocity × Velocity) → ℝ}
    (hPm : ∀ n, Measurable (P n)) (hQm : Measurable Q)
    (hPi : ∀ n, Integrable (P n) (μ.prod volume)) (hQi : Integrable Q (μ.prod volume))
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hPb : ∀ n, eLpNorm (P n) 1 (μ.prod volume) ≤ B)
    (hQb : eLpNorm Q 1 (μ.prod volume) ≤ B)
    (hprod : ∀ (a b : C(Velocity,ℝ)), HasCompactSupport a → HasCompactSupport b →
      Tendsto (fun n => eLpNorm (fun x =>
        pairTestAverage (tensorTest a b) (P n) x-pairTestAverage (tensorTest a b) Q x) 1 μ)
        atTop (𝓝 0))
    (k : C(Velocity × Velocity,ℝ)) (hk : HasCompactSupport k) :
    Tendsto (fun n => eLpNorm (fun x => pairTestAverage k (P n) x-pairTestAverage k Q x) 1 μ)
      atTop (𝓝 0) := by
  let ε : ℕ → ℝ := fun j => 1/((j:ℝ)+1)
  have hε j : 0 < ε j := by dsimp [ε]; positivity
  choose a ha he using (fun j => exists_supported_tensorSum_uniform k hk (hε j))
  have hac j := (ha j).hasCompactSupport
  have hδ : Tendsto (fun j => ENNReal.ofReal (ε j)*B) atTop (𝓝 0) := by
    have hr : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have ht := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hr) (Or.inr hB)
    simpa only [ENNReal.ofReal_zero,zero_mul] using ht
  apply strongL1_of_two_sided_approximations hδ
    (u := fun j n => pairTestAverage (a j) (P n)) (v := fun j => pairTestAverage (a j) Q)
  · intro j n
    change eLpNorm (fun x => pairTestAverage k (P n) x-pairTestAverage (a j) (P n) x) 1 μ ≤ _
    exact (pairTestAverage_uniform_error (hPm n) (hPi n) hk (hac j)
      (fun y => by rw [abs_sub_comm]; exact (he j y).le)).trans (mul_le_mul' le_rfl (hPb n))
  · intro j
    change eLpNorm (fun x => pairTestAverage (a j) Q x-pairTestAverage k Q x) 1 μ ≤ _
    exact (pairTestAverage_uniform_error hQm hQi (hac j) hk
      (fun y => (he j y).le)).trans (mul_le_mul' le_rfl hQb)
  · intro j
    exact strong_supported_tensor_pair_tests hPi hQi hprod (ha j)

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
