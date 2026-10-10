import OAI.Analysis.Brenier.Basic

namespace OAI

section

open MeasureTheory

namespace Problem358

/-- A measure concentrated on the graph of a measurable function is determined
by its first marginal. This is the last step in uniqueness of a transport plan. -/
theorem eq_graph_map_of_ae_on_graph
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (π : Measure (X × Y)) {T : X → Y} (hT : Measurable T)
    (hgraph : ∀ᵐ p ∂π, p.2 = T p.1) :
    π = Measure.map (fun x => (x, T x)) (Measure.map Prod.fst π) := by
  have hm : Measurable (fun x : X => (x, T x)) := measurable_id.prodMk hT
  rw [Measure.map_map hm measurable_fst]
  calc
    π = Measure.map id π := (Measure.map_id).symm
    _ = Measure.map ((fun x => (x, T x)) ∘ Prod.fst) π := by
      apply Measure.map_congr
      filter_upwards [hgraph] with p hp
      exact Prod.ext rfl hp

/-- The same reconstruction statement with an explicitly prescribed marginal. -/
theorem eq_graph_map_of_fst_eq_and_ae_on_graph
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {π : Measure (X × Y)} {ρ : Measure X} {T : X → Y}
    (hT : Measurable T) (hfst : Measure.map Prod.fst π = ρ)
    (hgraph : ∀ᵐ p ∂π, p.2 = T p.1) :
    π = Measure.map (fun x => (x, T x)) ρ := by
  rw [← hfst]
  exact eq_graph_map_of_ae_on_graph π hT hgraph

end Problem358

end

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem358

variable {d : ℕ} {ρ μ : Measure (E d)} {π : Measure (E d × E d)}

/-- A finite quadratic plan cost is an ordinary integrable squared distance. -/
theorem integrable_sqdist_of_cost_ne_top
    (h : quadraticPlanCost π ≠ ∞) :
    Integrable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) π := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (by fun_prop) (Filter.Eventually.of_forall fun p => sq_nonneg _)).mp
  exact h

/-- Conversion between the extended and real quadratic costs. -/
theorem quadraticPlanCost_eq_ofReal_integral
    (h : Integrable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) π) :
    quadraticPlanCost π = ENNReal.ofReal (∫ p, ‖p.1 - p.2‖ ^ 2 ∂π) := by
  exact (ofReal_integral_eq_lintegral_ofReal h
    (Filter.Eventually.of_forall fun p => sq_nonneg _)).symm

/-- Integrability of a separable dual potential under any coupling. -/
theorem dual_integrable_sum (hπ : IsCoupling ρ μ π)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ) :
    Integrable (fun p : E d × E d => f p.1 + g p.2) π := by
  have hf' : Integrable f (Measure.map Prod.fst π) := hπ.2.1.symm ▸ hf
  have hg' : Integrable g (Measure.map Prod.snd π) := hπ.2.2.symm ▸ hg
  exact (hf'.comp_measurable measurable_fst).add
    (hg'.comp_measurable measurable_snd)

/-- The integral of a separable dual potential depends only on the marginals. -/
theorem dual_integral_sum (hπ : IsCoupling ρ μ π)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ) :
    (∫ p, f p.1 + g p.2 ∂π) = (∫ x, f x ∂ρ) + ∫ y, g y ∂μ := by
  have hf' : Integrable f (Measure.map Prod.fst π) := hπ.2.1.symm ▸ hf
  have hg' : Integrable g (Measure.map Prod.snd π) := hπ.2.2.symm ▸ hg
  have hfi : Integrable (fun p : E d × E d => f p.1) π := hf'.comp_measurable measurable_fst
  have hgi : Integrable (fun p : E d × E d => g p.2) π := hg'.comp_measurable measurable_snd
  rw [integral_add hfi hgi]
  rw [← integral_map measurable_fst.aemeasurable hf'.aestronglyMeasurable,
    ← integral_map measurable_snd.aemeasurable hg'.aestronglyMeasurable,
    hπ.2.1, hπ.2.2]

/-- Weak Kantorovich duality for the problem's quadratic cost definition. -/
theorem dual_cost_lower_bound (hπ : IsCoupling ρ μ π)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ)
    (hbound : ∀ᵐ p ∂π, f p.1 + g p.2 ≤ ‖p.1 - p.2‖ ^ 2) :
    ENNReal.ofReal ((∫ x, f x ∂ρ) + ∫ y, g y ∂μ) ≤ quadraticPlanCost π := by
  by_cases htop : quadraticPlanCost π = ∞
  · simp [htop]
  have hc := integrable_sqdist_of_cost_ne_top htop
  rw [quadraticPlanCost_eq_ofReal_integral hc,
    ← dual_integral_sum hπ hf hg]
  exact ENNReal.ofReal_le_ofReal (integral_mono_ae (dual_integrable_sum hπ hf hg) hc hbound)

/-- A graph saturating a separable dual bound has exactly the dual cost. -/
theorem quadraticPlanCost_graph_eq_dual
    {T : E d → E d} (hT : Measurable T) (hpush : Measure.map T ρ = μ)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ)
    (heq : ∀ᵐ x ∂ρ, ‖x - T x‖ ^ 2 = f x + g (T x)) :
    quadraticPlanCost (graphPlan ρ T) =
      ENNReal.ofReal ((∫ x, f x ∂ρ) + ∫ y, g y ∂μ) := by
  have hg' : Integrable g (Measure.map T ρ) := hpush.symm ▸ hg
  have hgT : Integrable (fun x => g (T x)) ρ := hg'.comp_measurable hT
  have hc : Integrable (fun x => ‖x - T x‖ ^ 2) ρ := (hf.add hgT).congr (heq.mono fun x hx => hx.symm)
  unfold quadraticPlanCost graphPlan
  have hm : Measurable (fun x : E d => (x, T x)) := by fun_prop
  rw [lintegral_map (by fun_prop) hm]
  change (∫⁻ x, ENNReal.ofReal (‖x - T x‖ ^ 2) ∂ρ) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hc
    (Filter.Eventually.of_forall fun x => sq_nonneg _), integral_congr_ae heq,
    integral_add hf hgT, ← integral_map hT.aemeasurable hg'.aestronglyMeasurable,
    hpush]

/-- Dual attainment certifies optimality against every probability coupling. -/
theorem isQuadraticOptimalMap_of_dual
    {T : E d → E d} (hT : Measurable T) (hpush : Measure.map T ρ = μ)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ)
    (hbound : ∀ π : Measure (E d × E d), IsCoupling ρ μ π →
      ∀ᵐ p ∂π, f p.1 + g p.2 ≤ ‖p.1 - p.2‖ ^ 2)
    (heq : ∀ᵐ x ∂ρ, ‖x - T x‖ ^ 2 = f x + g (T x)) :
    IsQuadraticOptimalMap ρ μ T := by
  refine ⟨hT, hpush, fun π hπ => ?_⟩
  rw [quadraticPlanCost_graph_eq_dual hT hpush hf hg heq]
  exact dual_cost_lower_bound hπ hf hg (hbound π hπ)

end Problem358

end

noncomputable section

open MeasureTheory

namespace Problem358

/-- There is only one coupling with a fixed first marginal and a Dirac second marginal. -/
theorem coupling_dirac_eq_graphPlan_const {d : ℕ} {ρ : Measure (E d)}
    {π : Measure (E d × E d)} {y : E d}
    (hπ : IsCoupling ρ (Measure.dirac y) π) :
    π = graphPlan ρ (fun _ => y) := by
  apply eq_graph_map_of_fst_eq_and_ae_on_graph measurable_const hπ.2.1
  apply ae_of_ae_map (μ := π) (p := fun z => z = y) measurable_snd.aemeasurable
  rw [hπ.2.2]
  simp

/-- The constant map to a point is the unique quadratic optimal map to its Dirac law.
No moment assumption is necessary: every competing coupling is already the same graph. -/
theorem isUniqueQuadraticOptimalMap_const {d : ℕ} (ρ : Measure (E d))
    [IsProbabilityMeasure ρ] (y : E d) :
    IsUniqueQuadraticOptimalMap ρ (Measure.dirac y) (fun _ => y) := by
  constructor
  · refine ⟨measurable_const, ?_, ?_⟩
    · simp [Measure.map_const]
    · intro π hπ
      rw [coupling_dirac_eq_graphPlan_const hπ]
  · intro π hπ _
    exact coupling_dirac_eq_graphPlan_const hπ

/-- A probability measure supported on a singleton is the corresponding Dirac law. -/
theorem eq_dirac_of_supported_singleton {d : ℕ} (μ : Measure (E d))
    [IsProbabilityMeasure μ] (y : E d) (hμ : IsSupported μ {y}) :
    μ = Measure.dirac y := by
  have hae : ∀ᵐ x ∂μ, x = y := by
    exact ae_iff.mpr hμ
  calc
    μ = Measure.map id μ := Measure.map_id.symm
    _ = Measure.map (fun _ => y) μ := Measure.map_congr hae
    _ = Measure.dirac y := by simp [Measure.map_const]

/-- The same conclusion holds for any nonempty subsingleton support set. -/
theorem eq_dirac_of_supported_subsingleton {d : ℕ} (μ : Measure (E d))
    [IsProbabilityMeasure μ] {Y : Set (E d)} (hY : Y.Subsingleton)
    {y : E d} (hy : y ∈ Y) (hμ : IsSupported μ Y) :
    μ = Measure.dirac y := by
  apply eq_dirac_of_supported_singleton μ y
  have hae : ∀ᵐ x ∂μ, x ∈ Y := ae_iff.mpr hμ
  apply ae_iff.mp
  filter_upwards [hae] with x hx
  exact hY hx hy

/-- The singleton-target case of stability, for an arbitrary probability source. -/
theorem one_third_stability_of_subsingleton_target {d : ℕ}
    (ρ : Measure (E d)) [IsProbabilityMeasure ρ]
    {Y : Set (E d)} (hY : Y.Subsingleton) (hYn : Y.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ ν : Measure (E d)),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      IsSupported μ Y → IsSupported ν Y →
      ∃ Tμ Tν : E d → E d,
        IsUniqueQuadraticOptimalMap ρ μ Tμ ∧
        IsUniqueQuadraticOptimalMap ρ ν Tν ∧
        mapL2Dist ρ Tμ Tν ≤ C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ) := by
  obtain ⟨y, hy⟩ := hYn
  refine ⟨0, le_rfl, ?_⟩
  intro μ ν hμ hν hμY hνY
  let := hμ
  let := hν
  rw [eq_dirac_of_supported_subsingleton μ hY hy hμY,
    eq_dirac_of_supported_subsingleton ν hY hy hνY]
  refine ⟨fun _ => y, fun _ => y, isUniqueQuadraticOptimalMap_const ρ y,
    isUniqueQuadraticOptimalMap_const ρ y, ?_⟩
  simp [mapL2Dist]

end Problem358

end

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

variable {d : ℕ} {ρ μ : Measure (E d)} {π : Measure (E d × E d)}

/-- Equality in the integral dual bound forces saturation almost everywhere. -/
theorem dual_saturation_of_integral_eq
    (hπ : IsCoupling ρ μ π) {f g : E d → ℝ}
    (hf : Integrable f ρ) (hg : Integrable g μ)
    (hc : Integrable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) π)
    (hbound : ∀ᵐ p ∂π, f p.1 + g p.2 ≤ ‖p.1 - p.2‖ ^ 2)
    (heq : (∫ p, ‖p.1 - p.2‖ ^ 2 ∂π) =
      (∫ x, f x ∂ρ) + ∫ y, g y ∂μ) :
    ∀ᵐ p ∂π, f p.1 + g p.2 = ‖p.1 - p.2‖ ^ 2 := by
  apply (integral_eq_iff_of_ae_le (dual_integrable_sum hπ hf hg) hc hbound).mp
  rw [dual_integral_sum hπ hf hg]
  exact heq.symm

/-- A saturated dual bound whose equality locus is a graph identifies the full plan. -/
theorem eq_graphPlan_of_dual_saturation
    {T : E d → E d} (hT : Measurable T)
    (hπ : IsCoupling ρ μ π) {f g : E d → ℝ}
    (hf : Integrable f ρ) (hg : Integrable g μ)
    (hc : Integrable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) π)
    (hbound : ∀ᵐ p ∂π, f p.1 + g p.2 ≤ ‖p.1 - p.2‖ ^ 2)
    (heq : (∫ p, ‖p.1 - p.2‖ ^ 2 ∂π) =
      (∫ x, f x ∂ρ) + ∫ y, g y ∂μ)
    (hstrict : ∀ᵐ p ∂π,
      f p.1 + g p.2 = ‖p.1 - p.2‖ ^ 2 → p.2 = T p.1) :
    π = graphPlan ρ T := by
  apply eq_graph_map_of_fst_eq_and_ae_on_graph hT hπ.2.1
  filter_upwards [dual_saturation_of_integral_eq hπ hf hg hc hbound heq,
    hstrict] with p hp hs
  exact hs hp

/-- A dual value attained by a graph is nonnegative. -/
theorem dual_value_nonneg_of_graph
    {T : E d → E d} (hT : Measurable T) (hpush : Measure.map T ρ = μ)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ)
    (heq : ∀ᵐ x ∂ρ, ‖x - T x‖ ^ 2 = f x + g (T x)) :
    0 ≤ (∫ x, f x ∂ρ) + ∫ y, g y ∂μ := by
  have hg' : Integrable g (Measure.map T ρ) := hpush.symm ▸ hg
  have hgT : Integrable (fun x => g (T x)) ρ := hg'.comp_measurable hT
  rw [← hpush, integral_map hT.aemeasurable hg'.aestronglyMeasurable,
    ← integral_add hf hgT]
  apply integral_nonneg_of_ae
  filter_upwards [heq] with x hx
  rw [← hx]
  exact sq_nonneg _

/-- Strictness of a dual certificate identifies every optimal plan with its graph.
The strictness premise is only required almost everywhere for each coupling, so
null tie sets and support restrictions can be used directly. -/
theorem isUniqueQuadraticOptimalMap_of_dual
    {T : E d → E d} (hT : Measurable T) (hpush : Measure.map T ρ = μ)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ)
    (hbound : ∀ π : Measure (E d × E d), IsCoupling ρ μ π →
      ∀ᵐ p ∂π, f p.1 + g p.2 ≤ ‖p.1 - p.2‖ ^ 2)
    (heq : ∀ᵐ x ∂ρ, ‖x - T x‖ ^ 2 = f x + g (T x))
    (hstrict : ∀ π : Measure (E d × E d), IsCoupling ρ μ π →
      ∀ᵐ p ∂π, f p.1 + g p.2 = ‖p.1 - p.2‖ ^ 2 → p.2 = T p.1) :
    IsUniqueQuadraticOptimalMap ρ μ T := by
  have hopt := isQuadraticOptimalMap_of_dual hT hpush hf hg hbound heq
  refine ⟨hopt, fun π hπ hle => ?_⟩
  have hgraph := quadraticPlanCost_graph_eq_dual hT hpush hf hg heq
  have hfinite : quadraticPlanCost π ≠ ∞ := by
    apply ne_top_of_le_ne_top _ hle
    rw [hgraph]
    exact ENNReal.ofReal_ne_top
  have hc := integrable_sqdist_of_cost_ne_top hfinite
  have hcosteq : quadraticPlanCost π = quadraticPlanCost (graphPlan ρ T) :=
    le_antisymm hle (hopt.2.2 π hπ)
  have hvalue := dual_value_nonneg_of_graph hT hpush hf hg heq
  have hint : (∫ p, ‖p.1 - p.2‖ ^ 2 ∂π) =
      (∫ x, f x ∂ρ) + ∫ y, g y ∂μ := by
    have hh := (quadraticPlanCost_eq_ofReal_integral hc).symm.trans
      (hcosteq.trans hgraph)
    have hn : 0 ≤ ∫ p : E d × E d, ‖p.1 - p.2‖ ^ 2 ∂π :=
      integral_nonneg (fun p => sq_nonneg _)
    simpa only [ENNReal.toReal_ofReal hn, ENNReal.toReal_ofReal hvalue] using
      congrArg ENNReal.toReal hh
  exact eq_graphPlan_of_dual_saturation hT hπ hf hg hc (hbound π hπ)
    hint (hstrict π hπ)

end Problem358

end

end OAI
