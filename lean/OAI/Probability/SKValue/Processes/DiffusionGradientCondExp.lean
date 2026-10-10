import Mathlib
import OAI.Probability.SKValue.Equations.Shift

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators

lemma diffusion_gradient_condExp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t))
    {T K L Lu : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} {X : ℝ → Ω → ℝ}
    (hT1 : T≤1) (hLu : 0≤Lu) (h : GradientStripCore T γ u K L)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T,
      StronglyMeasurable[Filtration.natural B hBm t.toNNReal] (X t))
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      ∀ t∈Icc (0 : ℝ) T, X t ω=B t.toNNReal ω+∫ s in (0 : ℝ)..t, γ s*u s (X s ω))
    {a b : ℝ} (ha : a∈Icc (0 : ℝ) T) (hb : b∈Icc (0 : ℝ) T) (hab : a≤b) :
    μ[(fun ω ↦ u b (X b ω)) | Filtration.natural B hBm a.toNNReal]=ᵐ[μ](fun ω ↦ u a (X a ω)) := by
  let ℱ := Filtration.natural B hBm
  by_cases heq : a=b
  · subst b
    have hh := (h.smooth a ha).continuous.comp_stronglyMeasurable (hXM a ha)
    apply condExp_of_aestronglyMeasurable' (ℱ.le _) hh.aestronglyMeasurable
    exact Integrable.of_bound (hh.mono (ℱ.le _)).aestronglyMeasurable 1
      (Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le (h.bounded a ha _)))
  have hlt : a<b := lt_of_le_of_ne hab heq
  have hba : 0<b-a := sub_pos.mpr hlt
  have hba1 : b-a≤1 := by linarith [hb.2,ha.1]
  let Y := fun t : ℝ ↦ X (a+t)
  let W := fun t : ℝ ↦ fun ω ↦ X a ω+B (a.toNNReal+t.toNNReal) ω-B a.toNNReal ω
  have hmem (t : ℝ) (ht : t∈Icc (0 : ℝ) (b-a)) : a+t∈Icc (0 : ℝ) T := by
    constructor <;> linarith [ha.1,hb.2,ht.1,ht.2]
  have hLip' : ∀ s∈Icc (0 : ℝ) (b-a), ∀ t∈Icc (0 : ℝ) (b-a), ∀ x y,
      |u (a+s) x-u (a+t) y|≤Lu*(|s-t|+|x-y|) := by
    intro s hs t ht x y
    simpa only [add_sub_add_left_eq_sub] using hLip _ (hmem s hs) _ (hmem t ht) x y
  have hYM (t : ℝ) (ht : t∈Icc (0 : ℝ) (b-a)) :
      StronglyMeasurable[ℱ (a.toNNReal+t.toNNReal)] (Y t) := by
    have hh := hXM _ (hmem t ht)
    rw [Real.toNNReal_add ha.1 ht.1] at hh
    exact hh
  have hWM (t : ℝ) (_ht : t∈Icc (0 : ℝ) (b-a)) : AEStronglyMeasurable (W t) μ :=
    ((((hXM a ha).mono (ℱ.le _)).add (hBm _)).sub (hBm _)).aestronglyMeasurable
  have hW : ∀ s∈Icc (0 : ℝ) (b-a), ∀ t∈Icc (0 : ℝ) (b-a), ∀ ω,
      W t ω-W s ω=B (a.toNNReal+t.toNNReal) ω-B (a.toNNReal+s.toNNReal) ω := by
    intro s _ t _ ω
    dsimp [W]
    ring
  have hpaths' : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ Y t ω) (Icc (0 : ℝ) (b-a)) ∧
      IntervalIntegrable (fun s ↦ γ (a+s)*u (a+s) (Y s ω)) volume 0 (b-a) ∧
      ∀ t∈Icc (0 : ℝ) (b-a), Y t ω=W t ω+∫ s in (0 : ℝ)..t, γ (a+s)*u (a+s) (Y s ω) := by
    filter_upwards [hpaths] with ω hω
    have hT : 0≤T := ha.1.trans ha.2
    have hi := intervalIntegrable_substrip hT hω.2.1 ha hb
    refine ⟨hω.1.comp (continuous_const.add continuous_id).continuousOn hmem,?_,?_⟩
    · simpa only [sub_self,Y] using hi.comp_add_left a
    · intro t ht
      have hhalf := intervalIntegrable_substrip hT hω.2.1 ha (hmem t ht)
      have hleft := intervalIntegrable_substrip hT hω.2.1 ⟨le_rfl,hT⟩ ha
      have hsum := intervalIntegral.integral_add_adjacent_intervals hleft hhalf
      dsimp only [Y,W]
      rw [intervalIntegral.integral_comp_add_left (fun s ↦ γ s*u s (X s ω)) a,add_zero]
      rw [hω.2.2 _ (hmem t ht),hω.2.2 _ ha,Real.toNNReal_add ha.1 ht.1]
      linarith
  have hh := diffusion_gradient_condExp_local hB hBm a.toNNReal hba hba1 hLu
    (h.shift ha.1 hab hb.2) hLip' hYM hWM hW hpaths'
  simpa only [Y,add_sub_cancel,add_zero] using hh

end SKValue

namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators

lemma diffusion_gradient_stopped_martingale
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t))
    {T K L Lu : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} {X : ℝ → Ω → ℝ}
    (hT : 0≤T) (hT1 : T≤1) (hLu : 0≤Lu) (h : GradientStripCore T γ u K L)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T,
      StronglyMeasurable[Filtration.natural B hBm t.toNNReal] (X t))
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      ∀ t∈Icc (0 : ℝ) T, X t ω=B t.toNNReal ω+∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) :
    Martingale (fun t : ℝ≥0 ↦ fun ω ↦ u (min (t : ℝ) T) (X (min (t : ℝ) T) ω))
      (Filtration.natural B hBm) μ := by
  let ℱ := Filtration.natural B hBm
  have hmem (t : ℝ≥0) : min (t : ℝ) T∈Icc (0 : ℝ) T :=
    ⟨le_min t.coe_nonneg hT,min_le_right _ _⟩
  have htime (t : ℝ≥0) : (min (t : ℝ) T).toNNReal≤t := by
    have hh := Real.toNNReal_mono (min_le_left (t : ℝ) T)
    rw [Real.toNNReal_coe] at hh
    exact hh
  have hm (t : ℝ≥0) : StronglyMeasurable[ℱ t]
      (fun ω ↦ u (min (t : ℝ) T) (X (min (t : ℝ) T) ω)) :=
    ((h.smooth _ (hmem t)).continuous.comp_stronglyMeasurable (hXM _ (hmem t))).mono (ℱ.mono (htime t))
  have hi (t : ℝ≥0) : Integrable (fun ω ↦ u (min (t : ℝ) T) (X (min (t : ℝ) T) ω)) μ :=
    Integrable.of_bound ((hm t).mono (ℱ.le _)).aestronglyMeasurable 1
      (Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le (h.bounded _ (hmem t) _)))
  refine ⟨hm,?_⟩
  intro s t hst
  by_cases hs : (s : ℝ)≤T
  · have ha : (s : ℝ)∈Icc (0 : ℝ) T := ⟨s.coe_nonneg,hs⟩
    have hh := diffusion_gradient_condExp hB hBm hT1 hLu h hLip hXM hpaths ha (hmem t)
      (le_min (by exact_mod_cast hst) hs)
    rw [Real.toNNReal_coe] at hh
    simpa only [min_eq_left hs] using hh
  · have hs' : T≤(s : ℝ) := (lt_of_not_ge hs).le
    have ht : T≤(t : ℝ) := hs'.trans (by exact_mod_cast hst)
    have hh := condExp_of_aestronglyMeasurable' (ℱ.le s) (hm s).aestronglyMeasurable (hi s)
    simpa only [min_eq_right hs',min_eq_right ht] using hh

end SKValue

end

end OAI
