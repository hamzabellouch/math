import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIncomingLocalFinite
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMobiusSmooth

namespace OAI

/-! Joint spatial smoothness of the actual incoming arithmetic series.
The compact row bound makes the sum locally finite before differentiation. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma CubicThetaBottomRow.height_contDiffAt (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0<p.2) : ContDiffAt ℝ ∞ r.height p := by
  have he : r.height=(fun q => (cubicThetaMobius (cubicThetaPrincipalComplex r.completion) q).2) := by
    funext q
    rw [← cubicThetaBottomRow_height,r.completion_row]
  rw [he]
  exact contDiffAt_snd.comp p (cubicThetaMobius_contDiffAt _ hp)

lemma cubicThetaIncomingTerm_contDiffAt (r : CubicThetaBottomRow) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaIncomingTerm r q s) p := by
  have hh := r.height_contDiffAt hp
  have hc := cubicThetaCuspCutoff_smooth.contDiffAt.comp p hh
  have hpow := (cubicThetaHeightPower_analytic s (r.height_pos hp)).contDiffAt.comp p hh
  exact hc.mul (contDiffAt_const.mul hpow)

lemma cubicThetaPositive_compact_neighborhood {p : ℂ × ℝ} (hp : 0<p.2) :
    ∃ K : Set (ℂ × ℝ), K∈𝓝 p ∧ IsCompact K ∧ ∀ q∈K, 0<q.2 := by
  refine ⟨Metric.closedBall p (p.2/2),Metric.closedBall_mem_nhds p (half_pos hp),
    isCompact_closedBall _ _,?_⟩
  intro q hq
  have hd : dist q.2 p.2≤dist q p := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have hb := hd.trans (Metric.mem_closedBall.mp hq)
  rw [Real.dist_eq] at hb
  have h := (abs_le.mp hb).1
  linarith

theorem cubicThetaIncomingEisenstein_contDiffOn (s : ℂ) :
    ContDiffOn ℝ ∞ (fun p => cubicThetaIncomingEisenstein p s)
      {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaIncomingEisenstein_compact_sum hK hKpos
  have he : (fun q => cubicThetaIncomingEisenstein q s) =ᶠ[𝓝 p]
      (fun q => ∑ r∈S, cubicThetaIncomingTerm r q s) := by
    filter_upwards [hKn] with q hq
    exact hS q hq s
  have hd : ContDiffAt ℝ ∞ (fun q => ∑ r∈S, cubicThetaIncomingTerm r q s) p :=
    ContDiffAt.sum (fun r _ => cubicThetaIncomingTerm_contDiffAt r s hp)
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

end CubicFirstMoment

end

end OAI
