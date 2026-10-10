import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveVolterra
import OAI.MathematicalPhysics.Boltzmann.Branching.SecondCoreOffBands
import OAI.MathematicalPhysics.Boltzmann.Jets.CoreDensityTranslation
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace OAI

section

/-! # Combining the three regions in the two-gain estimate -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {X : Type*} [MeasurableSpace X]

/-- Exceptional axial intervals and transverse tails use the total kernel bound;
the remaining region uses the small second-kernel mass. -/
theorem integral_three_regions_le (μ : Measure X) {E T : Set X}
    (hE : MeasurableSet E) (hT : MeasurableSet T) {f : X → ℝ≥0∞}
    {B ε : ℝ≥0∞} (hB : ∀ x, f x ≤ B)
    (hgood : ∀ x, x ∉ E → x ∉ T → f x ≤ ε) :
    (∫⁻ x, f x ∂μ) ≤ B*μ E+B*μ T+ε*μ univ := by
  have hb : ∀ x, f x ≤ E.indicator (fun _ => B) x+T.indicator (fun _ => B) x+ε := by
    intro x
    by_cases he : x ∈ E
    · rw [indicator_of_mem he]
      calc
        f x ≤ B := hB x
        _ ≤ B+T.indicator (fun _ => B) x := le_self_add
        _ ≤ B+T.indicator (fun _ => B) x+ε := le_self_add
    by_cases ht : x ∈ T
    · rw [indicator_of_notMem he,zero_add,indicator_of_mem ht]
      exact (hB x).trans (le_add_of_nonneg_right (by positivity))
    · simpa only [indicator_of_notMem he,indicator_of_notMem ht,zero_add] using hgood x he ht
  calc
    _ ≤ ∫⁻ x, E.indicator (fun _ => B) x+T.indicator (fun _ => B) x+ε ∂μ :=
      lintegral_mono hb
    _ = _ := by
      rw [lintegral_add_left (show Measurable (fun x =>
          E.indicator (fun _ => B) x+T.indicator (fun _ => B) x) from
          (measurable_const.indicator hE).add (measurable_const.indicator hT)),
        lintegral_add_left (measurable_const.indicator hE),
        lintegral_indicator hE,lintegral_indicator hT]
      simp

/-- This criterion only uses explicit mass bounds for the two discarded regions
and a pointwise bound on the remaining second-kernel mass. -/
theorem integral_three_regions_tendsto {μ : ℕ → Measure X} {f : ℕ → X → ℝ≥0∞}
    {B C : ℝ≥0∞} (hB : B ≠ ∞) (hC : C ≠ ∞)
    (hbound : ∀ n x, f n x ≤ B) (hmass : ∀ n, μ n univ ≤ C)
    (hregions : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n in atTop, ∃ E T : Set X,
      MeasurableSet E ∧ MeasurableSet T ∧ μ n E ≤ ε ∧ μ n T ≤ ε ∧
      ∀ x, x ∉ E → x ∉ T → f n x ≤ ε) :
    Tendsto (fun n => ∫⁻ x, f n x ∂μ n) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hc : B+B+C ≠ ∞ := ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hB,hB⟩,hC⟩
  obtain ⟨δ,hδ,hs⟩ := ENNReal.exists_nnreal_pos_mul_lt hc hε.ne'
  filter_upwards [hregions δ (ENNReal.coe_pos.mpr hδ)] with n hn
  obtain ⟨E,T,hE,hT,he,ht,hgood⟩ := hn
  calc
    _ ≤ B*μ n E+B*μ n T+(δ : ℝ≥0∞)*μ n univ :=
      integral_three_regions_le (μ n) hE hT (hbound n) hgood
    _ ≤ B*δ+B*δ+(δ : ℝ≥0∞)*C := by gcongr; exact hmass n
    _ = (δ : ℝ≥0∞)*(B+B+C) := by ring
    _ ≤ ε := hs.le

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Bounded later factors in a two-gain integral -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem two_kernel_weighted_le (μ : Measure X) (ν : X → Measure Y)
    {f : X → Y → ℝ≥0∞} {B : ℝ≥0∞} (hB : B ≠ ∞) (hf : ∀ x y, f x y ≤ B) :
    (∫⁻ x, ∫⁻ y, f x y ∂ν x ∂μ) ≤ B*(∫⁻ x, ν x univ ∂μ) := by
  calc
    _ ≤ ∫⁻ x, B*ν x univ ∂μ := by
      apply lintegral_mono
      intro x
      simpa only [lintegral_const,mul_comm] using lintegral_mono (μ := ν x) (hf x)
    _ = _ := lintegral_const_mul' _ _ hB

theorem two_kernel_weighted_tendsto {μ : ℕ → Measure X} {ν : ℕ → X → Measure Y}
    {f : ℕ → X → Y → ℝ≥0∞} {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hf : ∀ n x y, f n x y ≤ B)
    (hlim : Tendsto (fun n => ∫⁻ x, ν n x univ ∂μ n) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x, ∫⁻ y, f n x y ∂ν n x ∂μ n) atTop (𝓝 0) := by
  have hbound (n : ℕ) := two_kernel_weighted_le (μ n) (ν n) hB (hf n)
  have hl : Tendsto (fun n => B*(∫⁻ x, ν n x univ ∂μ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (Or.inr hB)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
    (fun _ => bot_le) hbound

/-- Uniform smallness survives both time integrations. No measurability of the
parameter dependence is needed for this upper bound. -/
theorem two_time_integral_le {f : ℝ → ℝ → ℝ≥0∞} {a T : ℝ} {ε : ℝ≥0∞}
    (hf : ∀ t₁ ∈ Ioc a T, ∀ t₂ ∈ Ioc a t₁, f t₁ t₂ ≤ ε) :
    (∫⁻ t₁ in Ioc a T, ∫⁻ t₂ in Ioc a t₁, f t₁ t₂) ≤
      ε*(volume (Ioc a T))^2 := by
  calc
    _ ≤ ∫⁻ _t₁ in Ioc a T, ε*volume (Ioc a T) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t₁ ht₁
      calc
        _ ≤ ∫⁻ _t₂ in Ioc a t₁, ε := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t₂ ht₂
          exact hf t₁ ht₁ t₂ ht₂
        _ = ε*volume (Ioc a t₁) := by simp
        _ ≤ _ := mul_le_mul' le_rfl (measure_mono (Ioc_subset_Ioc_right ht₁.2))
    _ = _ := by
      simp only [lintegral_const,Measure.restrict_apply MeasurableSet.univ,
        univ_inter,pow_two]
      ring

theorem two_time_uniform_tendsto {f : ℕ → ℝ → ℝ → ℝ≥0∞} (a T : ℝ)
    (hsmall : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n in atTop,
      ∀ t₁ ∈ Ioc a T, ∀ t₂ ∈ Ioc a t₁, f n t₁ t₂ ≤ ε) :
    Tendsto (fun n => ∫⁻ t₁ in Ioc a T, ∫⁻ t₂ in Ioc a t₁, f n t₁ t₂) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hV : volume (Ioc a T) ≠ ∞ := measure_Ioc_lt_top.ne
  obtain ⟨δ,hδ,hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt (ENNReal.pow_ne_top hV) hε.ne'
  filter_upwards [hsmall δ (ENNReal.coe_pos.mpr hδ)] with n hn
  exact (two_time_integral_le hn).trans hδε.le

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Three-region decomposition for the actual two-core gain integral

The second core may be selected as a function of the intermediate velocity.
Only the explicit finite list of retained large scales is used. All estimates
are uniform in both times on a positive slab and in the positions.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AxialFlow

namespace BoltzmannNonuniqueness.JetCoreSheet

def ballisticSecondCoreMass (η K α γ q t₁ t₂ z : ℝ)
    (s d : Velocity → ℝ) (sign : Velocity → Bool) (y : Velocity → Transverse)
    (w : Velocity) : ℝ≥0∞ :=
  ChartKernel.offAxis (normalizedCoreKernel η K α γ (s w) (d w) q (sign w))
    ((t₂,(y w,z-(t₁-t₂)*axial w)),w) univ

/-- The small-scale threshold precedes the cardinality and large-scale radius.
This is the order of choices in the two-axial-gains lemma of §8. -/
theorem two_core_small_regions {K α γ q a ε : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hε : 0 < ε) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ J : ℕ, ∃ d₀ r₀ : ℝ, 0 < d₀ ∧ 0 < r₀ ∧
      ∀ {s₁ d₁ t₁ t₂ : ℝ}, 0 < s₁ → 0 < d₁ → d₁ ≤ 1/16 →
      a ≤ t₂ → t₂ ≤ t₁ →
      ∀ (η : ℝ) (sign₁ : Bool) (x : JetPrototype.Space) (v : Velocity)
        (S : Finset ℝ) (s₂ d₂ : Velocity → ℝ)
        (sign₂ : Velocity → Bool) (y₂ : Velocity → Transverse),
      ‖transverse v‖ ≤ r₀ → S.card ≤ J →
      (∀ w, 0 < s₂ w) → (∀ w, 0 < d₂ w) → (∀ w, d₂ w ≤ 1/16) →
      (∀ w, d₂ w ≤ d₀) → (∀ w, μ₀ ≤ s₂ w → s₂ w ∈ S) →
      ∃ E T : Set Velocity, MeasurableSet E ∧ MeasurableSet T ∧
        ChartKernel.offAxis (normalizedCoreKernel η K α γ s₁ d₁ q sign₁)
          ((t₁,x),v) E ≤ ENNReal.ofReal ε ∧
        ChartKernel.offAxis (normalizedCoreKernel η K α γ s₁ d₁ q sign₁)
          ((t₁,x),v) T ≤ ENNReal.ofReal ε ∧
        ∀ w, w ∉ E → w ∉ T →
          ballisticSecondCoreMass η K α γ q t₁ t₂ x.2 s₂ d₂ sign₂ y₂ w ≤
            ENNReal.ofReal ε := by
  obtain ⟨δ,hδ,hcollapsed⟩ := core_bands_small_of_card hK hα hγ hq₁ hq₂
    ha (half_pos hε) 5
  obtain ⟨μ₀,hμ₀,hsecond⟩ := second_core_small_off_bands hα hγ hq₁ hq₂ ha hδ
  refine ⟨μ₀,hμ₀,?_⟩
  intro J
  obtain ⟨b,hb,hprofile⟩ := core_bands_small_of_card hK hα hγ hq₁ hq₂
    ha (half_pos hε) (2*J)
  let A := slabAmplitude K α γ a
  have hA : 0 ≤ A := slabAmplitude_nonneg hK ha α γ
  have he : 0 < ε/(A+1) := div_pos hε (by positivity)
  obtain ⟨r,hr,hgood⟩ := hsecond b hb (ε/(A+1)) he
  obtain ⟨r₀,hr₀,htail⟩ := core_away_small_of_transverse hK hα hγ hq₁ hq₂ ha hr hε
  refine ⟨min δ b/4,r₀,div_pos (lt_min hδ hb) (by norm_num),hr₀,?_⟩
  intro s₁ d₁ t₁ t₂ hs₁ hd₁ hd₁max ht₂ htt η sign₁ x v S s₂ d₂ sign₂ y₂
    hv hS hs₂ hd₂ hd₂max hd₂small hmesh
  let E₁ := axial ⁻¹' bands (collapsedCenters α t₁ x.2) δ
  let E₂ := axial ⁻¹' bands (profileCenters α γ t₁ x.2 S) b
  let E := E₁ ∪ E₂
  let T := {w : Velocity | r ≤ ‖transverse w‖}
  have hE₁ : MeasurableSet E₁ :=
    (bands_measurableSet _ _).preimage ChartKernel.measurable_axial
  have hE₂ : MeasurableSet E₂ :=
    (bands_measurableSet _ _).preimage ChartKernel.measurable_axial
  refine ⟨E,T,hE₁.union hE₂,
    measurableSet_le measurable_const ChartKernel.measurable_transverse.norm,?_,?_,?_⟩
  · calc
      _ ≤ _ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) := add_le_add
        (hcollapsed hs₁ hd₁ hd₁max (ht₂.trans htt) η sign₁ x v _
          (collapsedCenters_card_le _ _ _))
        (hprofile hs₁ hd₁ hd₁max (ht₂.trans htt) η sign₁ x v _
          ((profileCenters_card_le _ _ _ _ _).trans (Nat.mul_le_mul_left 2 hS)))
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
        congr 1
        ring
  · exact htail hs₁ hd₁ hd₁max (ht₂.trans htt) η sign₁ x v hv
  · intro w hwE hwT
    have hw₁ : axial w ∉ bands (collapsedCenters α t₁ x.2) δ := fun h => hwE (Or.inl h)
    have hw₂ : axial w ∉ bands (profileCenters α γ t₁ x.2 S) b := fun h => hwE (Or.inr h)
    by_cases hw : transverse w = 0
    · unfold ballisticSecondCoreMass
      rw [ChartKernel.offAxis_axis _ _ hw]
      simp
    rw [ballisticSecondCoreMass,ChartKernel.offAxis_apply _ _ hw]
    apply (hgood hK (hs₂ w) (hd₂ w) (hd₂max w) (hd₂small w) ht₂ htt η
      (sign₂ w) (y₂ w) w S (hmesh w) hw (le_of_not_ge hwT) hw₁ hw₂).trans
    rw [← ENNReal.ofReal_mul (amplitude_nonneg hK (hs₂ w) (ha.le.trans ht₂) α γ)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (A+1)*(ε/(A+1)) := mul_le_mul_of_nonneg_right
        ((amplitude_le_slab hK ha (hs₂ w) ht₂ α γ).trans (by change A ≤ A+1; linarith)) he.le
      _ = ε := by field_simp

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Doubling the gain kernel in the positive iteration -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.PositiveIteration

theorem step_add_kernel (a : ℝ) (K L : Kernel KineticPhase Velocity)
    [IsSFiniteKernel K] {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) :
    step a (K+L) f = step a K f+step a L f := by
  funext z
  simp only [step,add_apply,lintegral_add_measure,Pi.add_apply]
  exact lintegral_add_left (step_inner_measurable K hf z) _

theorem iterate_two_add_self (a : ℝ) (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K] :
    iterate a (K+K) (fun _ => 1) 2 = fun z => 4*iterate a K (fun _ => 1) 2 z := by
  have h₁ := step_add_kernel a K K (measurable_const : Measurable (fun _ : KineticPhase => (1 : ℝ≥0∞)))
  have hm := step_measurable a K (measurable_const : Measurable (fun _ : KineticPhase => (1 : ℝ≥0∞)))
  funext z
  change step a (K+K) (step a (K+K) (fun _ => 1)) z = _
  rw [h₁,step_add a (K+K) hm,step_add_kernel a K K hm]
  simp only [Pi.add_apply]
  let A := step a K (step a K (fun _ => 1)) z
  change (A+A)+(A+A) = 4*A
  ring

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Reordering the two positive gain steps into their collision-time integral -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.PositiveIteration

def pairMass (K : Kernel Published.KineticPhase Velocity) (z : Published.KineticPhase)
    (t₂ : ℝ) : ℝ≥0∞ :=
  ∫⁻ w, K ((t₂,z.1.2-(z.1.1-t₂) • w),w) univ ∂K z

theorem integrate_second_step (a t₁ : ℝ) (x v : Velocity)
    (K : Kernel Published.KineticPhase Velocity) [IsSFiniteKernel K] :
    (∫⁻ w, step a K (fun _ => 1) ((t₁,x),w) ∂K ((t₁,x),v)) =
      ∫⁻ t₂ in Ioc a t₁, pairMass K ((t₁,x),v) t₂ := by
  have hm : Measurable (fun p : Velocity × ℝ => K ((p.2,x-(t₁-p.2) • p.1),p.1) univ) :=
    (K.measurable_coe MeasurableSet.univ).comp (by fun_prop)
  simp only [step,flight,lintegral_one,pairMass]
  exact lintegral_lintegral_swap hm.aemeasurable

theorem iterate_two_eq_pairMass (a : ℝ) (K : Kernel Published.KineticPhase Velocity)
    [IsSFiniteKernel K] (z : Published.KineticPhase) :
    iterate a K (fun _ => 1) 2 z =
      ∫⁻ t₁ in Ioc a z.1.1, ∫⁻ t₂ in Ioc a t₁, pairMass K (flight z t₁) t₂ := by
  change (∫⁻ t₁ in Ioc a z.1.1,
    ∫⁻ w, step a K (fun _ => 1) ((flight z t₁).1,w) ∂K (flight z t₁)) = _
  apply lintegral_congr
  intro t₁
  exact integrate_second_step a t₁ (flight z t₁).1.2 z.2 K

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Vanishing of the actual two-core velocity integral at an axial endpoint -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

/-- This is the velocity-integral part of the two-axial-gains lemma. The finite
list hypothesis is a scale-discretization condition, with no integral or
compactness conclusion assumed. Both collision times and positions may vary. -/
theorem two_core_axial_tendsto {K α γ q a : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2) (ha : 0 < a)
    (η s₁ d₁ t₁ t₂ D : ℕ → ℝ) (sign₁ : ℕ → Bool)
    (x : ℕ → JetPrototype.Space) (v : ℕ → Velocity)
    (s₂ d₂ : ℕ → Velocity → ℝ) (sign₂ : ℕ → Velocity → Bool)
    (y₂ : ℕ → Velocity → Transverse)
    (hs₁ : ∀ n, 0 < s₁ n) (hd₁ : ∀ n, 0 < d₁ n) (hd₁max : ∀ n, d₁ n ≤ 1/16)
    (ht₂ : ∀ n, a ≤ t₂ n) (htt : ∀ n, t₂ n ≤ t₁ n)
    (hs₂ : ∀ n w, 0 < s₂ n w) (hd₂ : ∀ n w, 0 < d₂ n w)
    (hd₂max : ∀ n w, d₂ n w ≤ 1/16) (hd₂D : ∀ n w, d₂ n w ≤ D n)
    (hD : Tendsto D atTop (𝓝 0))
    (hv : Tendsto (fun n => ‖transverse (v n)‖) atTop (𝓝 0))
    (hmesh : ∀ μ : ℝ, 0 < μ → ∃ J : ℕ, ∀ n, ∃ S : Finset ℝ,
      S.card ≤ J ∧ ∀ w, μ ≤ s₂ n w → s₂ n w ∈ S) :
    Tendsto (fun n => ∫⁻ w,
      ballisticSecondCoreMass (η n) K α γ q (t₁ n) (t₂ n) (x n).2
        (s₂ n) (d₂ n) (sign₂ n) (y₂ n) w
      ∂ChartKernel.offAxis (normalizedCoreKernel (η n) K α γ (s₁ n) (d₁ n) q (sign₁ n))
        ((t₁ n,x n),v n)) atTop (𝓝 0) := by
  let B := ENNReal.ofReal (growthConstant K α γ q/a)
  have htotal {s d t : ℝ} (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1/16) (ht : a ≤ t)
      (η : ℝ) (sign : Bool) (x : JetPrototype.Space) (v : Velocity) :
      ChartKernel.offAxis (normalizedCoreKernel η K α γ s d q sign) ((t,x),v) univ ≤ B := by
    apply (offAxisCoreKernel_time_bound hK hα hγ hs hd hdmax (ha.trans_le ht)
      hq₁ hq₂ η sign x v).trans
    exact ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_left (growthConstant_nonneg hK α γ q) ha ht)
  apply GainPullback.integral_three_regions_tendsto (B := B) (C := B)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · intro n w
    exact htotal (hs₂ n w) (hd₂ n w) (hd₂max n w) (ht₂ n) _ _ _ _
  · intro n
    exact htotal (hs₁ n) (hd₁ n) (hd₁max n) ((ht₂ n).trans (htt n)) _ _ _ _
  · intro ε hε
    obtain ⟨e,he,heε⟩ := ENNReal.exists_nnreal_pos_mul_lt
      (by simp : (1 : ℝ≥0∞) ≠ ∞) hε.ne'
    have he' : (0 : ℝ) < e := he
    have heε' : ENNReal.ofReal (e : ℝ) ≤ ε := by simpa using heε.le
    obtain ⟨μ,hμ,hregions⟩ := two_core_small_regions hK hα hγ hq₁ hq₂ ha he'
    obtain ⟨J,hJ⟩ := hmesh μ hμ
    obtain ⟨d₀,r₀,hd₀,hr₀,hr⟩ := hregions J
    filter_upwards [hD.eventually (gt_mem_nhds hd₀),hv.eventually (gt_mem_nhds hr₀)]
      with n hnD hnv
    obtain ⟨S,hS,hsS⟩ := hJ n
    obtain ⟨E,T,hE,hT,heE,heT,hgood⟩ := hr (hs₁ n) (hd₁ n) (hd₁max n)
      (ht₂ n) (htt n) (η n) (sign₁ n) (x n) (v n) S (s₂ n) (d₂ n) (sign₂ n) (y₂ n)
      hnv.le hS (hs₂ n) (hd₂ n) (hd₂max n) (fun w => (hd₂D n w).trans hnD.le) hsS
    exact ⟨E,T,hE,hT,heE.trans heε',heT.trans heε',
      fun w hwE hwT => (hgood w hwE hwT).trans heε'⟩

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
