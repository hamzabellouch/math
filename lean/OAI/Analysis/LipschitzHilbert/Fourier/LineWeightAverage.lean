import OAI.Analysis.LipschitzHilbert.Fourier.FiniteLineAverage
import OAI.Analysis.LipschitzHilbert.Phase.LineGridPrediction
import OAI.Analysis.LipschitzHilbert.Estimates.TopWeight
import OAI.Analysis.LipschitzHilbert.Estimates.WeightedAverage

namespace OAI

/-! Nested line averaging against the manuscript's actual top weight. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

namespace SlopeBox

theorem continuous_weight (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) :
    Continuous (T.weight K D) := by
  have hr : Continuous (fun z => 1 + T.radius z / K) := by
    unfold radius horizontal transverse
    fun_prop
  unfold weight
  apply continuous_const.mul
  exact hr.rpow_const fun z => Or.inl (ne_of_gt (by
    have h := T.radius_nonnegative z
    positivity))

/-- The top weight is comparable on a reference-line cell no longer
than the top. The constant depends only on the fixed decay exponent. -/
theorem line_weight_comparable (T : SlopeBox) (origin transverse x : ℝ)
    {K D H : ℝ} (hK : 1 ≤ K) (hD : 0 ≤ D) (hH : H ≤ T.length)
    (hx : x ∈ Ico origin (origin + H)) :
    Real.exp (-D) * T.weight K D (origin, transverse + T.slope * origin) ≤
      T.weight K D (x, transverse + T.slope * x) ∧
    T.weight K D (x, transverse + T.slope * x) ≤
      Real.exp D * T.weight K D (origin, transverse + T.slope * origin) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hshift : lineShift T.slope (x - origin) (origin, transverse + T.slope * origin) =
      (x, transverse + T.slope * x) := by
    ext <;> dsimp only [lineShift] <;> ring
  have hdist : |x - origin| ≤ T.length := by
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
    linarith [hx.2]
  have hlog := T.log_weight_same_slope hK hD hdist
    (origin, transverse + T.slope * origin)
  rw [hshift] at hlog
  obtain ⟨hl, hu⟩ := abs_le.mp hlog
  have hl' : -D + Real.log (T.weight K D (origin, transverse + T.slope * origin)) ≤
      Real.log (T.weight K D (x, transverse + T.slope * x)) := by linarith
  have hu' : Real.log (T.weight K D (x, transverse + T.slope * x)) ≤
      D + Real.log (T.weight K D (origin, transverse + T.slope * origin)) := by linarith
  constructor
  · have h := Real.exp_le_exp.mpr hl'
    simpa only [Real.exp_add, Real.exp_log (T.weight_pos hK0 _ _)] using h
  · have h := Real.exp_le_exp.mpr hu'
    simpa only [Real.exp_add, Real.exp_log (T.weight_pos hK0 _ _)] using h

end SlopeBox

namespace FiniteLineGrid

/-- The actual mesh product may be averaged against a top's decaying
weight. No cellwise weight-comparison hypothesis remains in the result. -/
theorem top_weight_average (g : FiniteLineGrid) (T : SlopeBox) (y : ℝ)
    {K D : ℝ} (hK : 1 ≤ K) (hD : 0 ≤ D) (hwidth : g.width ≤ T.length)
    (Γ : ℕ → ℝ → ℝ)
    (hΓ : ∀ n < g.depth, ∀ x, 0 ≤ Γ n x)
    (hconstant : ∀ n < g.depth, ∀ x z,
      g.index (n + 1) x = g.index (n + 1) z → Γ n x = Γ n z)
    (haverage : ∀ n < g.depth, ∀ i : Fin (g.branching ^ g.depth),
      (∫ x in {x | g.index n x = i}, Γ n x ∂volume.restrict g.root) ≤
        (volume.restrict g.root).real {x | g.index n x = i}) :
    Integrable (fun x => T.weight K D (x, y + T.slope * x) *
      ∏ n ∈ Finset.range g.depth, Γ n x) (volume.restrict g.root) ∧
    (∫ x in g.root, T.weight K D (x, y + T.slope * x) *
      ∏ n ∈ Finset.range g.depth, Γ n x) ≤
      Real.exp (2 * D) * ∫ x in g.root, T.weight K D (x, y + T.slope * x) := by
  let : IsFiniteMeasure (volume.restrict g.root) := isFiniteMeasure_restrict.mpr (by
    simp only [root, Real.volume_Ico, ENNReal.ofReal_ne_top, ne_eq, not_false_eq_true])
  let c := Real.exp (-D) * T.weight K D (g.origin, y + T.slope * g.origin)
  have hc : 0 ≤ c := (mul_pos (Real.exp_pos _) (T.weight_pos (by linarith) _ _)).le
  have hcompare : ∀ᵐ x ∂volume.restrict g.root,
      c ≤ T.weight K D (x, y + T.slope * x) ∧
      T.weight K D (x, y + T.slope * x) ≤ Real.exp (2 * D) * c := by
    filter_upwards [ae_restrict_mem (show MeasurableSet g.root from measurableSet_Ico)] with x hx
    have h := T.line_weight_comparable g.origin y x hK hD hwidth hx
    refine ⟨h.1, h.2.trans_eq ?_⟩
    dsimp only [c]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  exact weighted_average_le (volume.restrict g.root)
    (fun x => T.weight K D (x, y + T.slope * x)) _ hc (Real.exp_pos _).le
    ((T.continuous_weight (by linarith) D).comp (by fun_prop)).aestronglyMeasurable
    (g.integrable_product _ Γ hΓ hconstant)
    (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun n hn =>
      hΓ n (Finset.mem_range.mp hn) x)
    (hcompare.mono fun _ h => h.1) (hcompare.mono fun _ h => h.2)
    (g.average_product_le _ Γ hΓ hconstant haverage)

end FiniteLineGrid
end LipschitzHilbert

end

end OAI
