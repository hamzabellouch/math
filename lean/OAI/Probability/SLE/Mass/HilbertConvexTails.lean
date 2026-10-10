import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Order.MonotoneConvergence

namespace OAI

/-! Deterministic convex extraction in a Hilbert space. Nested closed
convex tail hulls have a common point, and finite convex combinations
of the original tails converge to that point. -/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace SLEExactGauge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma nested_closed_convex_intersection (K : ℕ → Set E)
    (hne : ∀ n, (K n).Nonempty) (hclosed : ∀ n, IsClosed (K n))
    (hconvex : ∀ n, Convex ℝ (K n)) (hanti : Antitone K)
    (B : ℝ) (hbound : ∀ n x, x ∈ K n → ‖x‖ ≤ B) :
    ∃ x, ∀ n, x ∈ K n := by
  have hex (n : ℕ) := exists_norm_eq_iInf_of_complete_convex (hne n)
    (hclosed n).isComplete (hconvex n) (0 : E)
  choose p hp hmin using hex
  have hleast (n : ℕ) (w : E) (hw : w ∈ K n) : ‖p n‖ ≤ ‖w‖ := by
    have hm : ‖p n‖ = ⨅ v : K n, ‖(v : E)‖ := by simpa only [zero_sub,norm_neg] using hmin n
    rw [hm]
    exact ciInf_le (show BddBelow (range (fun v : K n => ‖(v : E)‖)) from
      ⟨0,by rintro y ⟨v,rfl⟩; exact norm_nonneg _⟩) (⟨w,hw⟩ : K n)
  have hnormmono : Monotone (fun n => ‖p n‖^2) := by
    intro n m hnm
    exact pow_le_pow_left₀ (norm_nonneg _) (hleast n (p m) (hanti hnm (hp m))) 2
  have hnormbdd : BddAbove (range (fun n => ‖p n‖^2)) := by
    refine ⟨B^2,?_⟩
    rintro _ ⟨n,rfl⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound n (p n) (hp n)) 2
  have hsquare : CauchySeq (fun n => ‖p n‖^2) :=
    (tendsto_atTop_ciSup hnormmono hnormbdd).cauchySeq
  have hdist (n m : ℕ) (hnm : n ≤ m) :
      dist (p m) (p n)^2 ≤ ‖p m‖^2-‖p n‖^2 := by
    have hproj := (norm_eq_iInf_iff_real_inner_le_zero (hconvex n) (hp n)).mp
      (hmin n) (p m) (hanti hnm (hp m))
    simp only [zero_sub,inner_neg_left,inner_sub_right,
      real_inner_self_eq_norm_sq] at hproj
    rw [dist_eq_norm,norm_sub_sq_real,real_inner_comm]
    linarith
  have hcauchy : CauchySeq p := by
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hsquare (ε^2) (sq_pos_of_pos hε)
    refine ⟨N,fun n hn => ?_⟩
    have hh := hN n hn N le_rfl
    rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hnormmono hn))] at hh
    have hsq := hdist N n hn
    nlinarith [dist_nonneg (x := p n) (y := p N)]
  obtain ⟨x,hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨x,fun n => ?_⟩
  apply (hclosed n).mem_of_tendsto hx
  filter_upwards [eventually_ge_atTop n] with m hm
  exact hanti hm (hp m)

/-- The combinations use indices `n+i`, so every term is in the `n`-th
original tail. No weak-convergence or separability hypothesis is needed. -/
theorem exists_convex_tail_combinations (u : ℕ → E)
    (B : ℝ) (hB : ∀ n, ‖u n‖ ≤ B) :
    ∃ x : E, ∃ s : ℕ → Finset ℕ, ∃ w : ℕ → ℕ → ℝ,
      (∀ n i, i ∈ s n → 0 ≤ w n i) ∧
      (∀ n, ∑ i ∈ s n, w n i = 1) ∧
      (∀ n, dist (∑ i ∈ s n, w n i • u (n+i)) x < (1/2:ℝ)^n) ∧
      Tendsto (fun n => ∑ i ∈ s n, w n i • u (n+i)) atTop (𝓝 x) := by
  let K : ℕ → Set E := fun n => closedConvexHull ℝ (range (fun i => u (n+i)))
  have hne (n : ℕ) : (K n).Nonempty :=
    ⟨u (n+0),subset_closedConvexHull ⟨0,rfl⟩⟩
  have hclosed (n : ℕ) : IsClosed (K n) := isClosed_closedConvexHull
  have hconvex (n : ℕ) : Convex ℝ (K n) := convex_closedConvexHull
  have hanti : Antitone K := by
    intro n m hnm
    apply (closedConvexHull ℝ).monotone
    rintro _ ⟨i,rfl⟩
    refine ⟨m-n+i,?_⟩
    exact congrArg u (by omega)
  have hbound (n : ℕ) (x : E) (hx : x ∈ K n) : ‖x‖ ≤ B := by
    have hh : K n ⊆ closedBall 0 B := by
      apply closedConvexHull_min _ (convex_closedBall 0 B) isClosed_closedBall
      rintro _ ⟨i,rfl⟩
      simpa only [mem_closedBall,dist_zero_right] using hB (n+i)
    simpa only [mem_closedBall,dist_zero_right] using hh hx
  obtain ⟨x,hx⟩ := nested_closed_convex_intersection K hne hclosed hconvex hanti B hbound
  have happ (n : ℕ) : ∃ y ∈ convexHull ℝ (range (fun i => u (n+i))),
      dist y x < (1/2:ℝ)^n := by
    have hmem : x ∈ closure (convexHull ℝ (range (fun i => u (n+i)))) := by
      simpa only [K,closedConvexHull_eq_closure_convexHull] using hx n
    obtain ⟨y,hy,hyx⟩ := Metric.mem_closure_iff.mp hmem ((1/2:ℝ)^n) (by positivity)
    exact ⟨y,hy,by simpa only [dist_comm] using hyx⟩
  choose y hy hdist using happ
  have hcomb (n : ℕ) : ∃ s : Finset ℕ, ∃ w : ℕ → ℝ,
      (∀ i ∈ s, 0 ≤ w i) ∧ (∑ i ∈ s, w i = 1) ∧
      (∑ i ∈ s, w i • u (n+i)) = y n := by
    have hn := hy n
    rw [convexHull_range_eq_exists_affineCombination] at hn
    obtain ⟨s,w,hw,hs,hv⟩ := hn
    refine ⟨s,w,hw,hs,?_⟩
    simpa only [Finset.affineCombination_eq_linear_combination _ _ _ hs] using hv
  choose s w hw hs hsum using hcomb
  refine ⟨x,s,w,hw,hs,?_,?_⟩
  · intro n
    simpa only [hsum] using hdist n
  have hyconv : Tendsto y atTop (𝓝 x) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have he := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).eventually (gt_mem_nhds hε))
    obtain ⟨N,hN⟩ := eventually_atTop.mp he
    exact ⟨N,fun n hn => (hdist n).trans (hN n hn)⟩
  simpa only [hsum] using hyconv

end SLEExactGauge

end

end OAI
