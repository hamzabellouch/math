import OAI.Probability.GammaPassage.Environment
import OAI.Probability.GammaPassage.FirstMoment
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Set Filter

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}
variable {shape rate : ℝ}

/-- All edge weights are almost surely positive, by positivity of the marginal and countability. -/
theorem GammaEnvironment.ae_positive (h : GammaEnvironment shape rate P τ) :
    ∀ᵐ ω ∂P, ∀ e, 0 < τ e ω := by
  rw [ae_all_iff]
  intro e
  have hp : ∀ᵐ x ∂Measure.map (τ e) P, 0 < x := by
    rw [h.marginal e]
    exact gamma_ae_pos shape rate
  exact (ae_map_iff (h.measurable e).aemeasurable measurableSet_Ioi).mp hp

/-- Each Gamma edge weight is integrable. -/
theorem GammaEnvironment.integrable_edge (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (e : PlanarFPP.Edge) :
    Integrable (τ e) P := by
  have hi : Integrable (fun x : ℝ => x) (Measure.map (τ e) P) := by
    rw [h.marginal e]
    exact gamma_integrable_id hs hr
  simpa only [Function.comp_def] using hi.comp_aemeasurable (h.measurable e).aemeasurable

/-- The mean edge weight is `shape / rate`. -/
theorem GammaEnvironment.integral_edge (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (e : PlanarFPP.Edge) :
    (∫ ω, τ e ω ∂P) = shape / rate := by
  have he : (∫ x : ℝ, x ∂Measure.map (τ e) P) = ∫ ω, τ e ω ∂P :=
    integral_map (h.measurable e).aemeasurable measurable_id.aestronglyMeasurable
  rw [h.marginal e, gamma_integral_id hs hr] at he
  exact he.symm

/-- The cost of a fixed finite step list is integrable, including repeated edges. -/
theorem GammaEnvironment.integrable_pathCost (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (p : PlanarFPP.Vertex) (ds : List PlanarFPP.Step) :
    Integrable (fun ω => PlanarFPP.pathCost (fun e => τ e ω) p ds) P := by
  induction ds generalizing p with
  | nil =>
      let : IsProbabilityMeasure P := h.probability
      change Integrable (fun _ : Ω => (0 : ℝ)) P
      exact integrable_const (μ := P) (0 : ℝ)
  | cons d ds ih =>
      exact (h.integrable_edge hs hr (d.edge p)).add (ih (p + d.delta))

/-- Expected path cost counts edge traversals. The empty path has expectation zero. -/
theorem GammaEnvironment.integral_pathCost (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (p : PlanarFPP.Vertex) (ds : List PlanarFPP.Step) :
    (∫ ω, PlanarFPP.pathCost (fun e => τ e ω) p ds ∂P) =
      (ds.length : ℝ) * (shape / rate) := by
  induction ds generalizing p with
  | nil => simp [PlanarFPP.pathCost]
  | cons d ds ih =>
      change (∫ ω, τ (d.edge p) ω +
        PlanarFPP.pathCost (fun e => τ e ω) (p + d.delta) ds ∂P) = _
      rw [integral_add (h.integrable_edge hs hr (d.edge p))
        (h.integrable_pathCost hs hr (p + d.delta) ds),
        h.integral_edge hs hr (d.edge p), ih]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring

/-- Passage time is integrable by domination by the cost of one deterministic path. -/
theorem GammaEnvironment.integrable_passageTime (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (p q : PlanarFPP.Vertex) :
    Integrable (fun ω => PlanarFPP.passageTime (fun e => τ e ω) p q) P := by
  obtain ⟨ds, hend⟩ := PlanarFPP.exists_path p q
  apply (h.integrable_pathCost hs hr p ds).mono'
    (h.measurable_passageTime p q).aestronglyMeasurable
  filter_upwards [h.ae_positive] with ω hω
  have hn : ∀ e, 0 ≤ τ e ω := fun e => (hω e).le
  rw [Real.norm_eq_abs, abs_of_nonneg (PlanarFPP.passageTime_nonneg _ hn p q)]
  exact PlanarFPP.passageTime_le_cost _ hn p q ds hend

end GammaFPP

end OAI
