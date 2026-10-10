import OAI.Probability.GammaPassage.PathIntegrability
import OAI.Probability.GammaPassage.MGF
import OAI.Probability.GammaPassage.CheapPath
import OAI.Probability.FirstPassage.CoordinateTails
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped BigOperators

noncomputable def pathSecondMomentConstant (shape rate : ℝ) : ℝ :=
  8 * (2 : ℝ)^shape / rate^2

lemma square_le_gamma_exp (rate x : ℝ) (hr : 0 < rate) (hx : 0 ≤ x) :
    x^2 ≤ (8 / rate^2) * Real.exp ((rate/2)*x) := by
  have ht := Real.pow_div_factorial_le_exp ((rate/2)*x) (by positivity) 2
  norm_num at ht
  have ha : x^2 ≤ (8 * Real.exp ((rate/2)*x)) / rate^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    nlinarith
  convert ha using 1
  ring

lemma gamma_integrable_square_bound (shape rate : ℝ) (hs : 0 < shape) (hr : 0 < rate) :
    Integrable (fun x : ℝ => x^2) (gammaMeasure shape rate) := by
  apply ((gamma_integrable_exp hs hr (show rate/2 < rate by linarith)).const_mul
    (8 / rate^2)).mono' (by fun_prop)
  filter_upwards [gamma_ae_pos shape rate] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
  exact square_le_gamma_exp rate x hr hx.le

lemma gamma_integral_square_le (shape rate : ℝ) (hs : 0 < shape) (hr : 0 < rate) :
    (∫ x : ℝ, x^2 ∂gammaMeasure shape rate) ≤ pathSecondMomentConstant shape rate := by
  have hi := gamma_integrable_exp hs hr (show rate/2 < rate by linarith)
  have hb := integral_mono_ae (gamma_integrable_square_bound shape rate hs hr)
    (hi.const_mul (8 / rate^2)) (by
      filter_upwards [gamma_ae_pos shape rate] with x hx
      exact square_le_gamma_exp rate x hr hx.le)
  rw [integral_const_mul, gamma_integral_exp hs hr (show rate/2 < rate by linarith)] at hb
  have he : rate / (rate - rate/2) = 2 := by
    have hd : rate - rate/2 ≠ 0 := by linarith
    field_simp [hd]
    ring
  rw [he] at hb
  calc
    _ ≤ (8 / rate^2) * (2 : ℝ)^shape := hb
    _ = pathSecondMomentConstant shape rate := by
      unfold pathSecondMomentConstant
      ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

lemma GammaEnvironment.integrable_edge_square
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) (e : Edge) :
    Integrable (fun ω => (τ e ω)^2) P := by
  have hi : Integrable (fun x : ℝ => x^2) (Measure.map (τ e) P) := by
    rw [h.marginal e]
    exact gamma_integrable_square_bound shape rate hs hr
  simpa only [Function.comp_def] using hi.comp_aemeasurable (h.measurable e).aemeasurable

lemma GammaEnvironment.integral_edge_square_le
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) (e : Edge) :
    (∫ ω, (τ e ω)^2 ∂P) ≤ pathSecondMomentConstant shape rate := by
  have he := integral_map (μ := P) (h.measurable e).aemeasurable
    (f := fun x : ℝ => x^2) (by fun_prop)
  rw [h.marginal e] at he
  rw [← he]
  exact gamma_integral_square_le shape rate hs hr

lemma GammaEnvironment.pathCost_memLp_two
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (ds : List Step) :
    MemLp (fun ω => pathCost (fun e => τ e ω) p ds) 2 P := by
  let := h.probability
  induction ds generalizing p with
  | nil => exact memLp_const 0
  | cons d ds ih =>
      have he : MemLp (τ (d.edge p)) 2 P :=
        (memLp_two_iff_integrable_sq (h.measurable _).aestronglyMeasurable).mpr
          (h.integrable_edge_square hs hr _)
      exact he.add (ih (p + d.delta))

/-- The path cost is a sum over ordered traversal positions, including repeated edges. -/
lemma pathCost_eq_indexed_trace (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    pathCost w p ds =
      ∑ i : Fin ((trace p ds).map traversalEdge).length,
        w (((trace p ds).map traversalEdge).get i) := by
  rw [pathCost_trace_edge_sum]
  generalize ((trace p ds).map traversalEdge) = es
  conv_lhs => rw [← List.ofFn_get es]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]

/-- Finite Cauchy–Schwarz bounds the square of a sum for every real assignment. -/
lemma pathCost_square_le_indexed (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    (pathCost w p ds)^2 ≤ (ds.length : ℝ) *
      ∑ i : Fin ((trace p ds).map traversalEdge).length,
        (w (((trace p ds).map traversalEdge).get i))^2 := by
  rw [pathCost_eq_indexed_trace]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin ((trace p ds).map traversalEdge).length))
    (fun _ => (1 : ℝ)) (fun i => w (((trace p ds).map traversalEdge).get i))
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, trace_edge_length] using hc

/-- A polynomial second-moment bound for every deterministic finite step list. -/
theorem GammaEnvironment.pathCost_second_moment_le
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (ds : List Step) :
    (∫ ω, (pathCost (fun e => τ e ω) p ds)^2 ∂P) ≤
      pathSecondMomentConstant shape rate * (ds.length : ℝ)^2 := by
  let es := (trace p ds).map traversalEdge
  have hi (i : Fin es.length) : Integrable (fun ω => (τ (es.get i) ω)^2) P :=
    h.integrable_edge_square hs hr _
  have hsum : Integrable (fun ω => ∑ i : Fin es.length, (τ (es.get i) ω)^2) P :=
    integrable_finsetSum _ (fun i _ => hi i)
  have hb := integral_mono_ae (h.pathCost_memLp_two hs hr p ds).integrable_sq
    (hsum.const_mul (ds.length : ℝ))
    (Filter.Eventually.of_forall (fun ω => pathCost_square_le_indexed (fun e => τ e ω) p ds))
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)] at hb
  have he : (∑ i : Fin es.length, ∫ ω, (τ (es.get i) ω)^2 ∂P) ≤
      (ds.length : ℝ) * pathSecondMomentConstant shape rate := by
    calc
      _ ≤ ∑ _i : Fin es.length, pathSecondMomentConstant shape rate :=
        Finset.sum_le_sum (fun i _ => h.integral_edge_square_le hs hr _)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show es.length = ds.length from trace_edge_length p ds]
  calc
    _ ≤ (ds.length : ℝ) * (∑ i : Fin es.length, ∫ ω, (τ (es.get i) ω)^2 ∂P) := hb
    _ ≤ (ds.length : ℝ) * ((ds.length : ℝ) * pathSecondMomentConstant shape rate) :=
      mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
    _ = _ := by ring

/-- A polynomial second-moment bound for the deterministic coordinate path. -/
theorem GammaEnvironment.coordinatePath_second_moment_le
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) :
    (∫ ω, (pathCost (fun e => τ e ω) p (coordinatePath p q))^2 ∂P) ≤
      pathSecondMomentConstant shape rate * ((coordinatePath p q).length : ℝ)^2 :=
  h.pathCost_second_moment_le hs hr p (coordinatePath p q)

end GammaFPP

end OAI
