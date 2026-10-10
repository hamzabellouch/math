import Mathlib
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
namespace Release061
variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem c1_uniformlyOn_congr_on_open {K S : Set E} (hS : IsOpen S) (hKS : K ⊆ S)
    {f g : ι → E → F} {ψ : E → F} {l : Filter ι}
    (hEq : ∀ᶠ t in l, EqOn (f t) (g t) S)
    (hv : TendstoUniformlyOn f ψ l K)
    (hd : TendstoUniformlyOn (fun t => fderiv ℝ (f t)) (fderiv ℝ ψ) l K)
    (hf : ∀ᶠ t in l, ∀ x ∈ K, DifferentiableAt ℝ (f t) x) :
    TendstoUniformlyOn g ψ l K ∧
    TendstoUniformlyOn (fun t => fderiv ℝ (g t)) (fderiv ℝ ψ) l K ∧
    (∀ᶠ t in l, ∀ x ∈ K, DifferentiableAt ℝ (g t) x) := by
  have he (t : ι) (ht : EqOn (f t) (g t) S) (x : E) (hx : x ∈ K) :
      f t =ᶠ[𝓝 x] g t :=
    Filter.mem_of_superset (hS.mem_nhds (hKS hx)) fun y hy => ht hy
  refine ⟨hv.congr (hEq.mono fun t ht x hx => ht (hKS hx)),?_,?_⟩
  · exact hd.congr (hEq.mono fun t ht x hx => (he t ht x hx).fderiv_eq)
  · filter_upwards [hEq,hf] with t ht hf
    intro x hx
    exact (hf x hx).congr_of_eventuallyEq (he t ht x hx).symm

end Release061

namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

lemma scale_first_mem_ball {k : ℕ} {q : RealDiscParams k} {r t : ℝ}
    (hq : q ∈ ball 0 r) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (t • q.1,q.2) ∈ ball (0 : RealDiscParams k) r := by
  have hq' : max ‖q.1‖ ‖q.2‖ < r := by
    simpa only [mem_ball,dist_zero_right,Prod.norm_def] using hq
  simp only [mem_ball,dist_zero_right,Prod.norm_def]
  apply lt_of_le_of_lt _ hq'
  apply max_le_max _ le_rfl
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
  exact mul_le_of_le_one_left (norm_nonneg _) ht1

theorem scaledDisc_C1_limit {k : ℕ} {κ : realAlgebra}
    (hκ : ∀ θ, dist (circleCos θ) (-1 : ℝ) ≤ 1/2 →
      (2-2*circleCos θ)*realEvaluation θ κ = 1)
    {Y : RealDiscParams k → BoundarySpace k} (hY : ContDiffAt ℝ 1 Y 0)
    (hloc : ∀ᶠ q in 𝓝 0, ∀ θ, (1/2 : ℝ) < dist (circleCos θ) (-1 : ℝ) →
      ∀ i, realEvaluation θ (Y q i) = 0) :
    ∃ r : ℝ, 0 < r ∧
      TendstoUniformlyOn (scaledDisc Y) (limitModel κ Y) (𝓝[Ioi 0] 0) (closedBall 0 r) ∧
      TendstoUniformlyOn (fun t => fderiv ℝ (scaledDisc Y t)) (fderiv ℝ (limitModel κ Y))
        (𝓝[Ioi 0] 0) (closedBall 0 r) ∧
      (∀ᶠ t in 𝓝[Ioi 0] (0 : ℝ), ∀ q ∈ closedBall 0 r,
        DifferentiableAt ℝ (scaledDisc Y t) q) := by
  obtain ⟨r,hr,hv,hd,hdf⟩ := scaledModel_C1_limit κ hY
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hloc
  let R := min r (ε/2)
  have hR : 0 < R := lt_min hr (half_pos hε)
  have hRr : closedBall (0 : RealDiscParams k) R ⊆ closedBall 0 r :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hRε : closedBall (0 : RealDiscParams k) R ⊆ ball 0 ε :=
    closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have heq : ∀ᶠ t in 𝓝[Ioi 0] (0 : ℝ),
      EqOn (scaledModel κ Y t) (scaledDisc Y t) (ball 0 ε) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with t ht ht1
    intro q hq
    exact (scaledDisc_eq_model hκ (hsub (scale_first_mem_ball hq ht.le ht1.le)) ht ht1).symm
  refine ⟨R,hR,?_⟩
  apply c1_uniformlyOn_congr_on_open isOpen_ball hRε heq
  · intro u hu
    exact ((hv.mono hRr) u hu).filter_mono nhdsWithin_le_nhds
  · intro u hu
    exact ((hd.mono hRr) u hu).filter_mono nhdsWithin_le_nhds
  · filter_upwards [hdf.filter_mono nhdsWithin_le_nhds] with t ht q hq
    exact ht q (hRr hq)

end Release061.Wiener

end

end OAI
