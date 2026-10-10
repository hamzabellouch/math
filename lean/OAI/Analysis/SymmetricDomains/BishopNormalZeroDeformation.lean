import Mathlib
import OAI.Analysis.SymmetricDomains.TransverseCutoffs

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
namespace Release061.Wiener
open scoped Topology
open Set Filter

lemma evaluation_vector_norm_le {k : ℕ} (θ : Circle) (X : BoundarySpace k) :
    ‖(fun i => realEvaluation θ (X i))‖ ≤ ‖X‖ := by
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i =>
    (realEvaluation_bound θ (X i)).trans (norm_le_pi_norm X i))

lemma bishop_boundary_localization {k : ℕ}
    {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    (hf0 : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), f (Fin.cons 0 x) = 0)
    {lam η : realAlgebra}
    (hcut : ∀ θ, (1/2 : ℝ) ≤ dist (circleCos θ) (-1 : ℝ) →
      realEvaluation θ lam = 0 ∧ realEvaluation θ η = 0)
    {X Y : BishopParams k → BoundarySpace k} (hX0 : X 0 = 0)
    (hX : ContinuousAt X 0)
    (hEq : ∀ᶠ p in 𝓝 0, ∀ θ i, realEvaluation θ (Y p i) =
      f (Fin.cons (p.2.2.1*realEvaluation θ lam+p.2.2.2)
        (fun j => realEvaluation θ (X p j))) i+realEvaluation θ η*p.2.1 i) :
    ∀ᶠ p in 𝓝 0,
      (p.2.2.2 = 0 → ∀ θ, (1/2 : ℝ) < dist (circleCos θ) (-1 : ℝ) →
        ∀ i, realEvaluation θ (Y p i) = 0) ∧
      (p.2.2.1 = 0 → p.2.2.2 = 0 → ∀ i, Y p i = p.2.1 i • η) := by
  obtain ⟨ε,hε,hsmall⟩ := Metric.mem_nhds_iff.mp hf0
  have hn : ∀ᶠ p in 𝓝 0, ‖X p‖ < ε := by
    have hc : Tendsto (fun p => ‖X p‖) (𝓝 0) (𝓝 0) := by
      simpa only [hX0,norm_zero] using hX.norm.tendsto
    exact (tendsto_order.mp hc).2 ε hε
  filter_upwards [hEq,hn] with p hp hnp
  have hz (θ : Circle) : f (Fin.cons 0 (fun j => realEvaluation θ (X p j))) = 0 :=
    hsmall (by simpa only [Metric.mem_ball,dist_zero_right] using
      lt_of_le_of_lt (evaluation_vector_norm_le θ (X p)) hnp)
  refine ⟨?_,?_⟩
  · intro hδ θ hθ i
    obtain ⟨hl,hη⟩ := hcut θ hθ.le
    rw [hp θ i,hl,hη,hδ,mul_zero,zero_add,hz θ,Pi.zero_apply,zero_mul,add_zero]
  · intro hα hδ i
    apply realEvaluation_ext
    intro θ
    rw [hp θ i,hα,hδ,zero_mul,zero_add,hz θ,Pi.zero_apply,zero_add,map_smul]
    exact mul_comm _ _

def bishopNormal {k : ℕ} (κ : realAlgebra) (Y : BishopParams k → BoundarySpace k)
    (p : BishopParams k) : Fin k → ℝ := fun i => 2*realMean (κ*Y p i)

lemma bishopNormal_smooth {k : ℕ} (κ : realAlgebra)
    {Y : BishopParams k → BoundarySpace k} (hY : ContDiffAt ℝ ∞ Y 0) :
    ContDiffAt ℝ ∞ (bishopNormal κ Y) 0 := by
  apply contDiffAt_pi.mpr
  intro i
  dsimp only [bishopNormal]
  exact contDiffAt_const.mul (realMean.contDiff.contDiffAt.comp 0
    (contDiffAt_const.mul (contDiffAt_pi.mp hY i)))

lemma bishopNormal_zero_deformation {k : ℕ} {κ η : realAlgebra}
    {Y : BishopParams k → BoundarySpace k}
    (hY : ∀ᶠ p in 𝓝 0, p.2.2.1 = 0 → p.2.2.2 = 0 → ∀ i, Y p i = p.2.1 i • η) :
    ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × (Fin k → ℝ)),
      bishopNormal κ Y (q.1,q.2,0,0) = (2*realMean (κ*η)) • q.2 := by
  have ht : Tendsto (fun q : (Fin k → ℝ) × (Fin k → ℝ) =>
      (q.1,q.2,0,0) : _ → BishopParams k) (𝓝 0) (𝓝 0) := by
    exact (by fun_prop : ContinuousAt (fun q : (Fin k → ℝ) × (Fin k → ℝ) =>
      (q.1,q.2,0,0) : _ → BishopParams k) 0)
  filter_upwards [ht.eventually hY] with q hq
  funext i
  dsimp only [bishopNormal]
  rw [hq rfl rfl i,mul_smul_comm,map_smul]
  change 2*(q.2 i*realMean (κ*η)) = (2*realMean (κ*η))*q.2 i
  ring

end Release061.Wiener

end

end OAI
