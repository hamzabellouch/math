import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.UniformJetBoundsFiberComp

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples

lemma compact_normal_forward_bound (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    {K : Set NormalWaveSpace} (hK : IsCompact K) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q ∈ metricFrameSet g K, ∀ x : Fin 3 → ℝ, ‖x‖ ≤ R →
      ‖normalJetMap q.1 q.2 ((metricChristoffel g q.1).bilinearComp q.2 q.2)
        (normalWaveEquiv x)-q.1‖ ≤ C*‖x‖ := by
  let F := fun w : NormalWaveParameter × (Fin 3 → ℝ) =>
    normalJetMap w.1.1 w.1.2 ((metricChristoffel g w.1.1).bilinearComp w.1.2 w.1.2) (normalWaveEquiv w.2)
  have hF : ContDiff ℝ ∞ F := (contDiff_normalJetFamily g).comp
    (contDiff_fst.prodMk (normalWaveEquiv.contDiff.comp contDiff_snd))
  have hL : IsCompact (metricFrameSet g K ×ˢ Metric.closedBall (0 : Fin 3 → ℝ) R) :=
    (metricFrameSet_isCompact g hK).prod (isCompact_closedBall 0 R)
  obtain ⟨C,hC,hb⟩ := compact_fiber_jet_bound F hF hL 1
  refine ⟨C,hC,?_⟩
  intro q hq x hx
  have hFq : ContDiff ℝ ∞ (fun x => F (q,x)) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hd (v) (hv : v ∈ Metric.closedBall (0 : Fin 3 → ℝ) R) :
      ‖fderiv ℝ (fun x => F (q,x)) v‖ ≤ C := by
    rw [←norm_iteratedFDeriv_one]
    exact hb (q,v) ⟨hq,hv⟩ 1 le_rfl
  have hh := (convex_closedBall (0 : Fin 3 → ℝ) R).norm_image_sub_le_of_norm_fderiv_le
    (fun v _ => hFq.differentiable (by simp) v) hd (Metric.mem_closedBall_self hR)
    (show x ∈ Metric.closedBall (0 : Fin 3 → ℝ) R by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)
  simpa only [F,map_zero,normalJetMap_zero,sub_zero] using hh

lemma gaussian_coordinate_to_physical {c C n : ℝ} (hc : 0 ≤ c) (hC : 0 < C) (hn : 0 ≤ n)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ C*a) :
    Real.exp (-c*n*a^2) ≤ Real.exp (-(c/C^2)*n*b^2) := by
  apply Real.exp_le_exp.mpr
  have hsq : b^2 ≤ C^2*a^2 := by
    calc
      b^2 ≤ (C*a)^2 := by
        simpa only [pow_two] using mul_le_mul hba hba hb (mul_nonneg hC.le ha)
      _ = C^2*a^2 := mul_pow C a 2
  have hm := mul_le_mul_of_nonneg_left hsq (div_nonneg (mul_nonneg hc hn) (sq_nonneg C))
  have hnC : C^2 ≠ 0 := pow_ne_zero _ hC.ne'
  have he : (c*n/C^2)*(C^2*a^2) = c*n*a^2 := by field_simp
  rw [he] at hm
  calc
    -c*n*a^2 = -(c*n*a^2) := by ring
    _ ≤ -((c*n/C^2)*b^2) := neg_le_neg hm
    _ = -(c/C^2)*n*b^2 := by ring
end YauCounterexamples
end

end OAI
