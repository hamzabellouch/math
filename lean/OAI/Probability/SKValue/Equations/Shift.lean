import Mathlib
import OAI.Probability.SKValue.Processes.DiffusionGradientWeakMartingaleLocal

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

lemma GradientStripCore.shift {T K L a b : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (h : GradientStripCore T γ u K L) (ha : 0≤a) (hab : a≤b) (hb : b≤T) :
    GradientStripCore (b-a) (fun t ↦ γ (a+t)) (fun t ↦ u (a+t)) K L := by
  have hT : 0≤T := ha.trans (hab.trans hb)
  have hmem (t : ℝ) (ht : t∈Icc (0 : ℝ) (b-a)) : a+t∈Icc (0 : ℝ) T := by
    constructor <;> linarith [ht.1,ht.2]
  have ha' : a∈Icc (0 : ℝ) T := ⟨ha,hab.trans hb⟩
  have hb' : b∈Icc (0 : ℝ) T := ⟨ha.trans hab,hb⟩
  refine ⟨h.K_nonneg,h.L_nonneg,fun t ht ↦ h.gamma_nonneg _ (hmem t ht),?_,
    fun t ht ↦ h.smooth _ (hmem t ht),fun t ht ↦ h.bounded _ (hmem t ht),
    fun t ht ↦ h.second_bound _ (hmem t ht),fun t ht ↦ h.third_bound _ (hmem t ht),
    fun t ht ↦ h.product_bound _ (hmem t ht),?_,?_,?_,?_,?_⟩
  · intro s hs t ht hst
    exact h.gamma_mono (hmem s hs) (hmem t ht) (add_le_add le_rfl hst)
  · intro t ht s hs x y
    simpa only [add_sub_add_left_eq_sub] using h.second_lipschitz _ (hmem t ht) _ (hmem s hs) x y
  · intro t ht s hs x y
    simpa only [add_sub_add_left_eq_sub] using h.product_lipschitz _ (hmem t ht) _ (hmem s hs) x y
  · intro x
    have hi := intervalIntegrable_substrip hT (h.second_integrable x) ha' hb'
    simpa only [sub_self] using hi.comp_add_left a
  · intro x
    have hi := intervalIntegrable_substrip hT (h.product_integrable x) ha' hb'
    simpa only [sub_self] using hi.comp_add_left a
  · intro t ht s hs x
    rw [intervalIntegral.integral_comp_add_left
      (fun r ↦ (1/2 : ℝ)*deriv (deriv (u r)) x+γ r*(u r x*deriv (u r) x)) a]
    exact h.pde _ (hmem t ht) _ (hmem s hs) x

lemma diffusion_gradient_condExp_local
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) (a : ℝ≥0)
    {T K L Lu : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} {X W : ℝ → Ω → ℝ}
    (hT : 0<T) (hT1 : T≤1) (hLu : 0≤Lu)
    (h : GradientStripCore T γ u K L)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T,
      StronglyMeasurable[Filtration.natural B hBm (a+t.toNNReal)] (X t))
    (hWM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (W t) μ)
    (hW : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ ω,
      W t ω-W s ω=B (a+t.toNNReal) ω-B (a+s.toNNReal) ω)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      ∀ t∈Icc (0 : ℝ) T, X t ω=W t ω+∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) :
    μ[(fun ω ↦ u T (X T ω)) | Filtration.natural B hBm a]=ᵐ[μ](fun ω ↦ u 0 (X 0 ω)) := by
  let ℱ := Filtration.natural B hBm
  have hm (t : ℝ) (ht : t∈Icc (0 : ℝ) T) :
      StronglyMeasurable[ℱ (a+t.toNNReal)] (fun ω ↦ u t (X t ω)) :=
    (h.smooth t ht).continuous.comp_stronglyMeasurable (hXM t ht)
  have hi (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : Integrable (fun ω ↦ u t (X t ω)) μ := by
    apply Integrable.of_bound ((hm t ht).mono (ℱ.le _)).aestronglyMeasurable 1
    filter_upwards [] with ω
    exact (Real.norm_eq_abs _).trans_le (h.bounded t ht _)
  have h0m : StronglyMeasurable[ℱ a] (fun ω ↦ u 0 (X 0 ω)) := by
    have hh := hm 0 ⟨le_rfl,hT.le⟩
    rw [Real.toNNReal_zero,add_zero] at hh
    exact hh
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le a) (hi T ⟨hT.le,le_rfl⟩)
    (fun s _ _ ↦ (hi 0 ⟨le_rfl,hT.le⟩).integrableOn) _ h0m.aestronglyMeasurable
  intro s hs _
  have hF : StronglyMeasurable[ℱ a] (s.indicator (fun _ : Ω ↦ (1 : ℝ))) :=
    stronglyMeasurable_const.indicator hs
  have hFb (ω : Ω) : |s.indicator (fun _ : Ω ↦ (1 : ℝ)) ω|≤1 := by
    by_cases hω : ω∈s <;> simp [hω]
  have heq := diffusion_gradient_weak_martingale_local hB hBm a hT hT1 hLu (by norm_num : (0:ℝ)≤1)
    h hLip hXM hWM hW hpaths hF hFb
  have hprod (t : ℝ) : (fun ω ↦ s.indicator (fun _ : Ω ↦ (1 : ℝ)) ω*u t (X t ω))=
      s.indicator (fun ω ↦ u t (X t ω)) := by
    funext ω
    by_cases hω : ω∈s <;> simp [hω]
  rw [hprod T,hprod 0,integral_indicator (ℱ.le a s hs),integral_indicator (ℱ.le a s hs)] at heq
  exact heq.symm

end SKValue

end

end OAI
