import OAI.Analysis.LipschitzHilbert.Trees.SourceRadialTelescoping

namespace OAI

/-! The literal radial logarithmic loss has integral O(epsilon), uniformly
in the number of eligible levels. This is the scalar integral used by the
common-translation boundary average. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem nearbyEligibleMass_measurable_radius (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (i : ℕ) (s : ℝ) (x : X) :
    Measurable (fun r : ℝ => g.nearbyEligibleMass tops slope precision cutoff weight i r s x) := by
  simp only [nearbyEligibleMass,nearbyEligibleTops,Finset.sum_filter]
  apply Finset.measurable_sum
  intro t _
  by_cases he : g.eligible cutoff (precision t) i
  · simp only [he,true_and]
    exact measurable_const.piecewise measurableSet_Ioi measurable_const
  · simp only [he,false_and,ite_false]
    exact measurable_const

theorem radial_log_ratio_integral_le (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (N : ℕ) (top : τ) (htop : top ∈ tops)
    (he : ∀ i < N, g.eligible cutoff (precision top) i) (x : X) :
    let loss := fun b => ∑ i ∈ Finset.range N, Real.log
      (g.nearbyEligibleMass tops slope precision cutoff weight i (epsilon*g.width i) (slope top) x /
        g.nearbyEligibleMass tops slope precision cutoff weight i (b*g.width i) (slope top) x)
    IntegrableOn loss (Ioo 0 epsilon) volume ∧
      (∫ b in Ioo 0 epsilon, loss b) ≤
        2*epsilon*Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  dsimp only
  let loss := fun b => ∑ i ∈ Finset.range N, Real.log
    (g.nearbyEligibleMass tops slope precision cutoff weight i (epsilon*g.width i) (slope top) x /
      g.nearbyEligibleMass tops slope precision cutoff weight i (b*g.width i) (slope top) x)
  let B := Real.log ((∑ t ∈ tops, weight t x)/weight top x)
  let depth := geometricBoundaryDepth epsilon (g.branching:ℝ)⁻¹
  have hB : 0 ≤ B := Real.log_nonneg ((one_le_div (hw top x)).mpr
    (Finset.single_le_sum (fun t _ => (hw t x).le) htop))
  have hG : (2:ℝ) ≤ g.branching := by exact_mod_cast g.branching_ge_two
  have hG0 : 0 < (g.branching:ℝ) := by linarith
  have hinv0 : 0 ≤ (g.branching:ℝ)⁻¹ := inv_nonneg.mpr hG0.le
  have hinv1 : (g.branching:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hid : Integrable depth volume := geometricBoundaryDepth_integrable hepsilon hinv0 hinv1
  have hdepth0 (b : ℝ) : 0 ≤ depth b := tsum_nonneg fun j => geometricBoundaryLayer_nonneg _ _ _ _
  have hlossMeas : Measurable loss := by
    apply Finset.measurable_sum
    intro i _
    exact (measurable_const.div ((g.nearbyEligibleMass_measurable_radius tops slope precision cutoff
      weight i (slope top) x).comp (measurable_id.mul_const (g.width i)))).log
  have hloss0 (b : ℝ) (hb : b ∈ Ioo 0 epsilon) : 0 ≤ loss b := by
    apply Finset.sum_nonneg
    intro i hi
    have hbi := g.nearbyEligibleMass_self_le tops slope precision cutoff weight
      (fun t x => (hw t x).le) i top htop (he i (Finset.mem_range.mp hi))
      (mul_pos hb.1 (g.width_pos i)) x
    apply Real.log_nonneg
    apply (one_le_div ((hw top x).trans_le hbi)).mpr
    exact g.nearbyEligibleMass_le_of_scale tops slope precision cutoff weight hp
      (fun t x => (hw t x).le) le_rfl (mul_le_mul_of_nonneg_right hb.2.le (g.width_pos i).le)
      (slope top) x
  have hbound (b : ℝ) (hb : b ∈ Ioo 0 epsilon) : loss b ≤ depth b*B :=
    g.radial_log_ratio_sum_le_depth tops slope precision cutoff weight hp hw epsilon b hepsilon hb.1
      N top htop he x
  have hi : IntegrableOn loss (Ioo 0 epsilon) volume :=
    ((hid.mul_const B).restrict (s := Ioo 0 epsilon)).mono' hlossMeas.aestronglyMeasurable
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with b hb
        rw [Real.norm_eq_abs,abs_of_nonneg (hloss0 b hb)]
        exact hbound b hb)
  refine ⟨hi,?_⟩
  apply (integral_mono_ae hi ((hid.mul_const B).restrict (s := Ioo 0 epsilon)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with b hb
    exact hbound b hb)).trans
  have hfull : (∫ b in Ioo 0 epsilon, depth b*B) ≤ ∫ b, depth b*B :=
    integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall fun b => mul_nonneg (hdepth0 b) hB) (hid.mul_const B)
  apply hfull.trans
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right (integral_geometricBoundaryDepth_le hepsilon.le hG) hB

end LipschitzHilbert.AngularGrid

end

end OAI
