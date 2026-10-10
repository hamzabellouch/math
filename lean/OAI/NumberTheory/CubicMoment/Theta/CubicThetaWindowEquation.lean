import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHighWindowSeries
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingEquation

namespace OAI

/-! The compact incoming window satisfies its exact global differential
equation, with the original forcing minus the high annular forcing. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaIncomingWindowTerm_equation (r : CubicThetaBottomRow) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint x y v) s+
        cubicThetaForcingTerm r (cubicThetaCartesianPoint x y v) s-
        cubicThetaHighWindowTerm r (cubicThetaCartesianPoint x y v) s := by
  have hf : ContDiffAt ℝ 2 (cubicThetaWindowHeight s)
      (cubicThetaRowHeightCoordinates r x y v) :=
    (cubicThetaWindowHeight_smooth s).contDiffAt.of_le (by norm_num)
  have he : (fun a b t => cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint a b t) s)=
      (fun a b t => star r.phase*cubicThetaWindowHeight s
        (cubicThetaRowHeightCoordinates r a b t)) := by
    funext a b t
    unfold cubicThetaIncomingWindowTerm cubicThetaEisensteinTerm
      cubicThetaWindowHeight cubicThetaRowHeightCoordinates
    ring
  rw [he,cubicThetaHyperbolicOperator_const_mul,cubicThetaRowHeight_operator r x y hv hf,
    cubicThetaWindowHeight_equation s 0 0]
  unfold cubicThetaIncomingWindowTerm cubicThetaEisensteinTerm cubicThetaWindowHeight
    cubicThetaForcingTerm cubicThetaHighWindowTerm cubicThetaRowHeightCoordinates
  ring

private lemma window_coordinate_smooth (r : CubicThetaBottomRow) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ContDiffAt ℝ 2 (fun t => cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint t y v) s) x ∧
    ContDiffAt ℝ 2 (fun t => cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint x t v) s) y ∧
    ContDiffAt ℝ 2 (fun t => cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint x y t) s) v := by
  have hr := cubicThetaIncomingWindowTerm_contDiffAt r s (p:=cubicThetaCartesianPoint x y v) hv
  have hx : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint t y v) :=
    (Complex.ofRealCLM.contDiff.add contDiff_const).prodMk contDiff_const
  have hy : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint x t v) :=
    (contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)).prodMk contDiff_const
  have ht : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint x y t) :=
    contDiff_const.prodMk contDiff_id
  exact ⟨(hr.comp x hx.contDiffAt).of_le (by norm_num),
    (hr.comp y hy.contDiffAt).of_le (by norm_num),
    (hr.comp v ht.contDiffAt).of_le (by norm_num)⟩

lemma cubicThetaIncomingWindowFinite_equation (S : Finset CubicThetaBottomRow)
    (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => ∑ r∈S, cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*(∑ r∈S, cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint x y v) s)+
        (∑ r∈S, cubicThetaForcingTerm r (cubicThetaCartesianPoint x y v) s)-
        ∑ r∈S, cubicThetaHighWindowTerm r (cubicThetaCartesianPoint x y v) s := by
  have hcoords := fun r => window_coordinate_smooth r s x y hv
  rw [cubicThetaHyperbolicOperator_finite S
    (fun r a b t => cubicThetaIncomingWindowTerm r (cubicThetaCartesianPoint a b t) s) x y v
    (fun r _ => (hcoords r).1) (fun r _ => (hcoords r).2.1) (fun r _ => (hcoords r).2.2)]
  simp_rw [cubicThetaIncomingWindowTerm_equation _ s x y hv]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]

theorem cubicThetaIncomingWindow_equation (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHyperbolicOperator
      (fun a b t => cubicThetaIncomingWindow (cubicThetaCartesianPoint a b t) s) x y v=
      s*(s-2)*cubicThetaIncomingWindow (cubicThetaCartesianPoint x y v) s+
        cubicThetaForcingSeries (cubicThetaCartesianPoint x y v) s-
        cubicThetaHighWindowSeries (cubicThetaCartesianPoint x y v) s := by
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood
    (p:=cubicThetaCartesianPoint x y v) hv
  obtain ⟨S,hS⟩ := cubicThetaIncomingRows_compact hK hKpos
  have hw (p) (hp : p∈K) : cubicThetaIncomingWindow p s=∑ r∈S, cubicThetaIncomingWindowTerm r p s := by
    apply tsum_eq_sum
    intro r hr
    exact mul_eq_zero_of_left (cubicThetaIncomingWindowCutoff_low (hS p hp r hr).le) _
  have hf (p) (hp : p∈K) : cubicThetaForcingSeries p s=∑ r∈S, cubicThetaForcingTerm r p s := by
    apply tsum_eq_sum
    intro r hr
    exact mul_eq_zero_of_right _ (cubicThetaIncomingForcing_zero s (Or.inl (hS p hp r hr)))
  have hh (p) (hp : p∈K) : cubicThetaHighWindowSeries p s=∑ r∈S, cubicThetaHighWindowTerm r p s := by
    apply tsum_eq_sum
    intro r hr
    exact mul_eq_zero_of_right _ (cubicThetaHighWindowForcing_low s (by linarith [hS p hp r hr]))
  have he : (fun p => cubicThetaIncomingWindow p s)=ᶠ[𝓝 (cubicThetaCartesianPoint x y v)]
      (fun p => ∑ r∈S, cubicThetaIncomingWindowTerm r p s) := by
    filter_upwards [hKn] with p hp
    exact hw p hp
  have hpK : cubicThetaCartesianPoint x y v∈K := mem_of_mem_nhds hKn
  rw [cubicThetaHyperbolicOperator_germ x y v he,
    cubicThetaIncomingWindowFinite_equation S s x y hv,
    ← hw _ hpK,← hf _ hpK,← hh _ hpK]

end CubicFirstMoment

end

end OAI
