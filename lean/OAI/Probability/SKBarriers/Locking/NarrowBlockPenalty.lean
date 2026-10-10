import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.ConstantWeightMean
import OAI.Probability.SKBarriers.Locking.NarrowScheduleEndpoint
import OAI.Probability.SKBarriers.Locking.NarrowTimeBlocks
import OAI.Probability.SKBarriers.Scalar.NegativePenalty

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open Set
namespace SK.Analytic

theorem TimeChainOn.raw_mass_interval {α : ℝ → ℝ} (hα : Monotone α) {s t : ℝ} (l : TimeChainOn α s t) :
    ∀ p∈rawTimeChain l.chain,p.1∈Icc (α s) (α t) := by
  apply rawTimeChain_mass
  intro p hp
  have H := l.models.mass_bounds hα hp (l.positive p hp)
  change α s ≤ p.1 ∧ p.1 ≤ α t
  simpa only [l.duration,add_sub_cancel] using H

namespace NarrowTimeBlocks
variable {α : ℝ → ℝ} {r h q : ℝ} (B : NarrowTimeBlocks α r h q)

theorem crossPenalty_lower (hα : Monotone α) (hh : 0<h) {a θ : ℝ} (ha : 0 ≤ a) (hθ : 0 ≤ θ) :
    α r*(2*a*θ+θ^2)-a^2*(α (r+h)-α (r-h)) ≤ narrowCrossPenalty (B.c a) (B.v θ) (B.w a) := by
  have hn : h≠0 := ne_of_gt hh
  have hstats := B.cross_stats hn a θ
  have hc : weightedCrossPenalty (B.c a) 0=(a/h)^2*rawPenalty B.l 0 := by
    simp [c,weightedCrossPenalty_append]
  have hv : weightedCrossPenalty (B.v θ) a=(θ/h)^2*rawPenalty B.j 0+2*a*(θ/h)*rawArea B.j := by
    simp [v,weightedCrossPenalty_append,constantWeightChain_penalty_offset]
  have hw : weightedCrossPenalty (B.w a) a=(a/h)^2*rawPenalty B.j (-h) := by
    have he : (-a/h)*(-h)=a := by field_simp
    have H := constantWeightChain_penalty (-a/h) B.j (-h)
    rw [he] at H
    simpa only [w,weightedCrossPenalty_append,weightedCrossPenalty_zeroWeight,add_zero,div_pow,neg_sq] using H
  have HL := (rawPenalty_bounds B.l (B.left.raw_mass_interval hα) (q:=0) le_rfl).1
  have HJ := (rawPenalty_bounds B.j (B.right.raw_mass_interval hα) (q:=0) le_rfl).1
  have HW := (rawPenalty_negative_bounds B.j (B.right.raw_mass_interval hα) (q:=-h) (by rw [B.j_variance]; linarith)).1
  have HA := (rawArea_bounds B.j (B.right.raw_mass_interval hα)).1
  simp only [B.l_variance,B.j_variance,zero_add,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero] at HL HJ HA
  rw [B.j_variance] at HW
  have NL : α (r-h)*a^2 ≤ (a/h)^2*rawPenalty B.l 0 := by
    calc
      _ = (a/h)^2*(α (r-h)*h^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left HL (sq_nonneg _)
  have NJ : α r*θ^2 ≤ (θ/h)^2*rawPenalty B.j 0 := by
    calc
      _ = (θ/h)^2*(α r*h^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left HJ (sq_nonneg _)
  have NW : -α (r+h)*a^2 ≤ (a/h)^2*rawPenalty B.j (-h) := by
    calc
      _ = (a/h)^2*(α (r+h)*((-h+h)^2-(-h)^2)) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left HW (sq_nonneg (a/h))
  have NA : 2*a*θ*α r ≤ 2*a*(θ/h)*rawArea B.j := by
    calc
      _ = (2*a*(θ/h))*(α r*h) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left HA (by positivity)
  rw [narrowCrossPenalty,hstats.1,hc,hv,hw]
  nlinarith

end NarrowTimeBlocks

end SK.Analytic

end
end

end OAI
