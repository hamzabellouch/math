import Mathlib
import OAI.Analysis.SymmetricDomains.BishopPathInterior
import OAI.Analysis.SymmetricDomains.ScaledModelC1Limit

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

def regularizedSlice {k : ℕ} (Y : BishopParams k → BoundarySpace k) (α δ : ℝ)
    (q : RealDiscParams k) : BoundarySpace k := Y (q.1,q.2,α,δ)

lemma regularizedSlice_smooth {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    {ε : ℝ} (D : LocalBishopData k f ε) {α δ : ℝ} {q : RealDiscParams k}
    (hp : (q.1,q.2,α,δ) ∈ ball 0 D.radius) :
    ContDiffAt ℝ 1 (regularizedSlice D.Y α δ) q := by
  exact ((D.smoothY _ hp).contDiffAt (isOpen_ball.mem_nhds hp)).comp q (by fun_prop)

lemma scaledDisc_regularized_joint_smooth {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    {ε : ℝ} (D : LocalBishopData k f ε) (α t : ℝ) {q : ℝ × RealDiscParams k}
    (hp : (t • q.2.1,q.2.2,α,q.1) ∈ ball 0 D.radius) :
    ContDiffAt ℝ 1 (fun p : ℝ × RealDiscParams k =>
      scaledDisc (regularizedSlice D.Y α p.1) t p.2) q := by
  have hY := ((D.smoothY _ hp).contDiffAt (isOpen_ball.mem_nhds hp)).comp q
    (show ContDiffAt ℝ 1 (fun p : ℝ × RealDiscParams k => (t • p.2.1,p.2.2,α,p.1)) q by fun_prop)
  apply ContDiffAt.const_smul
  apply contDiffAt_pi.mpr
  intro i
  change ContDiffAt ℝ 1 (fun p => constantDisc ((t • p.2.1) i) (radialPoint t)+
    realSchwarz (D.Y (t • p.2.1,p.2.2,α,p.1) i) (radialPoint t)) q
  apply ContDiffAt.add
  · simp only [constantDisc_apply]
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp q (by
      change ContDiffAt ℝ 1 (fun p : ℝ × RealDiscParams k => t * p.2.1 i) q
      fun_prop)
  · exact (ContinuousMap.evalCLM ℝ (radialPoint t)).contDiff.contDiffAt.comp q
      (realSchwarz.contDiff.contDiffAt.comp q (contDiffAt_pi.mp hY i))

lemma scaledDisc_delta_C1_limit {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    {ε : ℝ} (D : LocalBishopData k f ε) {α t r : ℝ}
    (hr : r < D.radius) (hα : |α| < D.radius) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    TendstoUniformlyOn (fun δ => scaledDisc (regularizedSlice D.Y α δ) t)
      (scaledDisc (regularizedSlice D.Y α 0) t) (𝓝 0) (closedBall 0 r) ∧
      TendstoUniformlyOn (fun δ => fderiv ℝ (scaledDisc (regularizedSlice D.Y α δ) t))
        (fderiv ℝ (scaledDisc (regularizedSlice D.Y α 0) t)) (𝓝 0) (closedBall 0 r) := by
  let Φ : ℝ × RealDiscParams k → BishopParams k := fun p => (t • p.2.1,p.2.2,α,p.1)
  let S := Φ ⁻¹' ball 0 D.radius
  have hS : IsOpen S := isOpen_ball.preimage (show Continuous Φ by fun_prop)
  apply Release061.c1_family_uniformly_compact hS
    (fun p hp => (scaledDisc_regularized_joint_smooth D α t hp).contDiffWithinAt)
    (isCompact_closedBall _ _)
  rintro ⟨δ,q⟩ ⟨hδ,hq⟩
  have hδ0 : δ = 0 := mem_singleton_iff.mp hδ
  subst δ
  have hqnorm : ‖q‖ ≤ r := mem_closedBall_zero_iff.mp hq
  apply bishopParams_mem_ball _ _ hα (by simpa only [abs_zero] using D.radius_pos)
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
    have hb : ‖q.1‖ ≤ ‖q‖ := norm_fst_le q
    exact (mul_le_of_le_one_left (norm_nonneg _) ht1).trans_lt ((hb.trans hqnorm).trans_lt hr)
  · exact ((norm_snd_le q).trans hqnorm).trans_lt hr

end Release061.Wiener

end

end OAI
