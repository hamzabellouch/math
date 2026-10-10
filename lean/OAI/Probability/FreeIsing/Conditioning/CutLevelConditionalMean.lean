import OAI.Probability.FreeIsing.Estimates.BalancedLatentMean
import OAI.Probability.FreeIsing.Trees.NoisyCutLevelIndependence

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367.RootedBroadcast

local instance cutLevelConditionalMeanMeasurableSingletonIsingSpin :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
local instance cutLevelConditionalMeanIsProbabilityLabelMeasure (d : ℕ) :
    IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  infer_instance

theorem cutSpins_coordinate_fair {d : ℕ} {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) (c : TreeShell d n) (a : IsingSpin) :
    ((labelMeasure d).map (cutSpins theta n)) {s | s c = a} = (1 / 2 : ℝ≥0∞) := by
  rw [Measure.map_apply (measurable_cutSpins d theta n)
    (measurableSet_eq_fun (measurable_pi_apply c) measurable_const)]
  have h := (freeIsingMeasure_hasFreeIsingLaw d h0 h1).marginal c.1 a
  rw [freeIsingMeasure, Measure.map_apply (measurable_factor d theta)
    (measurableSet_eq_fun (measurable_pi_apply c.1) measurable_const)] at h
  change (labelMeasure d) {U | factor theta U c.1 = a} = _
  change (labelMeasure d) {U | factor theta U c.1 = a} = _ at h
  simpa using h

theorem condExp_noisy_factor_cone_le_two_integral {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (c : TreeShell d n)
    (F : (DescendantVertex c.1 → IsingSpin) × (DescendantVertex c.1 → A) → ℝ)
    (hF : Measurable F) (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) :
    ∀ᵐ z ∂(labelMeasure d).prod (Measure.infinitePi ν),
      (((labelMeasure d).prod (Measure.infinitePi ν))[
        (fun z : (TreeVertex d → ℝ) × (TreeVertex d → A) =>
          F ((fun v => factor theta z.1 v.1), fun v => z.2 v.1)) |
        (inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
          (fun z => cutSpins theta n z.1)]) z ≤
      2 * ∫ w : (TreeVertex d → ℝ) × (TreeVertex d → A),
        F ((fun v => factor theta w.1 v.1), fun v => w.2 v.1)
          ∂(labelMeasure d).prod (Measure.infinitePi ν) := by
  let S := TreeShell d n → IsingSpin
  let R := (e : TreeShell d n) →
    (StrictDescendantVertex e.1 → ℝ) × (DescendantVertex e.1 → A)
  let rho := (labelMeasure d).map (cutSpins theta n)
  let muR := Measure.infinitePi (fun e : TreeShell d n =>
    (Measure.infinitePi (fun _ : StrictDescendantVertex e.1 => uniform01)).prod
      (Measure.infinitePi (fun v : DescendantVertex e.1 => ν v.1)))
  let e : (TreeVertex d → ℝ) × (TreeVertex d → A) → S × R :=
    fun z => (cutSpins theta n z.1,
      fun c => (cutLabels z.1 c, fun v => z.2 v.1))
  have he : MeasurePreserving e ((labelMeasure d).prod (Measure.infinitePi ν))
      (rho.prod muR) :=
    ⟨((measurable_cutSpins d theta n).comp measurable_fst).prodMk
      (by unfold cutLabels; fun_prop), map_cutSpins_cutLabels_noises theta n ν⟩
  let G : IsingSpin × R → ℝ := fun p =>
    F (coneFactor theta c.1 (p.1, (p.2 c).1), (p.2 c).2)
  have hG : Measurable G :=
    hF.comp (((measurable_coneFactor theta c.1).comp
      (measurable_fst.prodMk
        (measurable_fst.comp ((measurable_pi_apply c).comp measurable_snd)))).prodMk
      (measurable_snd.comp ((measurable_pi_apply c).comp measurable_snd)))
  have h := condExp_binary_channel_comp_le_two_integral
    ((labelMeasure d).prod (Measure.infinitePi ν)) rho muR e he
    (fun s : S => s c) (measurable_pi_apply c)
    (cutSpins_coordinate_fair h0 h1 n c) G hG (fun p => hbound _)
  have hfun : (fun z => G ((e z).1 c, (e z).2)) =
      (fun z : (TreeVertex d → ℝ) × (TreeVertex d → A) =>
        F ((fun v => factor theta z.1 v.1), fun v => z.2 v.1)) := by
    funext z
    apply congrArg F
    apply Prod.ext
    · exact (factor_cone_representation theta c.1 z.1).symm
    · rfl
  rw [hfun] at h
  exact h

end Problem367.RootedBroadcast

namespace Problem367

local instance cutLevelConditionalMeanFreeIsingMeasurableSingletonIsingSpin :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem freeIsingMeasure_condExp_cutLevel_observable_le_two_integral
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (c : TreeShell d n)
    (F : (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → ℝ)
    (hF : Measurable F) (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) :
    ∀ᵐ z ∂(freeIsingMeasure d theta).prod (Measure.infinitePi ν),
      (((freeIsingMeasure d theta).prod (Measure.infinitePi ν))[
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          F ((fun v => z.1 v.1), fun v => z.2 v.1)) |
        (inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
          (fun z => fun e : TreeShell d n => z.1 e.1)]) z ≤
      2 * ∫ w : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
        F ((fun v => w.1 v.1), fun v => w.2 v.1)
          ∂(freeIsingMeasure d theta).prod (Measure.infinitePi ν) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  let P := (freeIsingMeasure d theta).prod (Measure.infinitePi ν)
  let Q := (labelMeasure d).prod (Measure.infinitePi ν)
  let e : (TreeVertex d → ℝ) × (TreeVertex d → A) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → A) :=
    Prod.map (RootedBroadcast.factor theta) id
  let H : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → ℝ :=
    fun z => F ((fun v => z.1 v.1), fun v => z.2 v.1)
  let S : (TreeVertex d → IsingSpin) × (TreeVertex d → A) →
      TreeShell d n → IsingSpin := fun z c => z.1 c.1
  have hS : Measurable S := by fun_prop
  have hH : Measurable H := hF.comp (by fun_prop)
  have hInt : Integrable H P := by
    apply Integrable.of_bound hH.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbound _).1]
      exact (hbound _).2)
  have hf : MeasurePreserving (RootedBroadcast.factor theta)
      (labelMeasure d) (freeIsingMeasure d theta) :=
    ⟨RootedBroadcast.measurable_factor d theta, rfl⟩
  have he : MeasurePreserving e Q P := hf.prod (MeasurePreserving.id (Measure.infinitePi ν))
  have hpull := condExp_comp_measurePreserving Q P e he
    ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap S)
    hS.comap_le hInt
  have hMean : (∫ x, H (e x) ∂Q) = ∫ z, H z ∂P := by
    rw [← he.map_eq]
    exact (integral_map he.measurable.aemeasurable hH.aestronglyMeasurable).symm
  have hsource := RootedBroadcast.condExp_noisy_factor_cone_le_two_integral
    h0 h1 n ν c F hF hbound
  change ∀ᵐ z ∂P, (P[H | MeasurableSpace.comap S inferInstance]) z ≤
    2 * ∫ w, H w ∂P
  have hgoal : ∀ᵐ z ∂Q.map e,
      (P[H | MeasurableSpace.comap S inferInstance]) z ≤ 2 * ∫ w, H w ∂P := by
    apply (ae_map_iff he.measurable.aemeasurable
      (measurableSet_le (stronglyMeasurable_condExp.mono hS.comap_le).measurable
        measurable_const)).mpr
    filter_upwards [hpull, hsource] with z hz hzbound
    have hmeanbound : (Q[H ∘ e | (MeasurableSpace.comap S inferInstance).comap e]) z ≤
        2 * ∫ x, H (e x) ∂Q := by
      simp only [MeasurableSpace.comap_comp, Function.comp_def, S, H, e,
        Prod.map_fst, Prod.map_snd, id_eq]
      exact hzbound
    rw [hz, hMean] at hmeanbound
    exact hmeanbound
  simpa only [he.map_eq] using hgoal

theorem HasFreeIsingLaw.condExp_cutLevel_observable_le_two_integral
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (c : TreeShell d n)
    (F : (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → ℝ)
    (hF : Measurable F) (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) :
    ∀ᵐ z ∂μ.prod (Measure.infinitePi ν),
      ((μ.prod (Measure.infinitePi ν))[
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          F ((fun v => z.1 v.1), fun v => z.2 v.1)) |
        (inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
          (fun z => fun e : TreeShell d n => z.1 e.1)]) z ≤
      2 * ∫ w : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
        F ((fun v => w.1 v.1), fun v => w.2 v.1) ∂μ.prod (Measure.infinitePi ν) := by
  have heq := hμ.eq_freeIsingMeasure h0 h1
  subst μ
  exact freeIsingMeasure_condExp_cutLevel_observable_le_two_integral h0 h1 n ν c F hF hbound

end Problem367

end

end OAI
