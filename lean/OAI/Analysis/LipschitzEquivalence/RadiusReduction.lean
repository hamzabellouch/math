import OAI.Analysis.LipschitzEquivalence.Multipliers

namespace OAI

universe uM

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem radius_escape_step {μ : ℕ → Space M} {ε : ℝ} (hε : 0 < ε)
    (hfail : ∀ R : ℝ, 0 < R → ∃ i, ¬ Approximable (μ i) (Metric.closedBall 0 R) ε)
    (p : ℕ) (r : ℝ) : ∃ i : ℕ, ∃ s : ℝ, ∃ g : M → ℝ,
      p < i ∧ r < s ∧ LipschitzWith 3 g ∧ g 0 = 0 ∧
      (∀ x, dist x 0 ≤ r → g x = 0) ∧ (∀ x, s ≤ dist x 0 → g x = 0) ∧
      ∀ hg : LipschitzWith 3 g, ε/2 < |test (normalized g hg) (μ i)| := by
  classical
  obtain ⟨R,hr,hR,hprefix⟩ := prefix_radius_approx μ hε (p+1) r
  obtain ⟨i,hi⟩ := hfail R hR
  have hip : p < i := by
    by_contra h
    exact hi (hprefix i (Nat.lt_succ_of_le (le_of_not_gt h)))
  have hfar : ∀ ν : Space M, ν ∈ supported (Metric.closedBall 0 R) → ε ≤ ‖μ i-ν‖ := by
    intro ν hν
    exact le_of_not_gt (fun h => hi ⟨ν,hν,h⟩)
  obtain ⟨f,hf,hf0,hfR,hlarge⟩ := exists_vanishing_test (Metric.closedBall 0 R) (μ i) hfar
  obtain ⟨a,ha⟩ := exists_finite_approx (μ i) (show 0 < ε/16 by positivity)
  obtain ⟨T,hT,hA⟩ := finite_bounded (A := a.support)
  let s : ℝ≥0 := ⟨2*(T+|r|+1),by positivity⟩
  have hs : 0 < s := by change 0 < 2*(T+|r|+1); positivity
  let g : M → ℝ := fun x => f x * cutoff 0 s x
  have hg : LipschitzWith 3 g := by
    simpa only [mul_one] using cutoff_product_lipschitz 0 hs f hf hf0
  refine ⟨i,s,g,hip,?_,hg,by simp [g,hf0],?_,?_,?_⟩
  · change r < 2*(T+|r|+1)
    linarith [le_abs_self r,abs_nonneg r]
  · intro x hx
    have hz := hfR x (show x ∈ Metric.closedBall 0 R from hx.trans hr)
    simp [g,hz]
  · intro x hx
    simp [g,cutoff_zero 0 hs hx]
  · intro hg'
    let K : Set M := insert 0 (a.support : Set M)
    have he (x : M) (hx : x ∈ K) : f x = g x := by
      rcases hx with rfl | hx
      · simp [g,hf0]
      · have hdist : dist x 0 ≤ (s : ℝ)/2 := by
          have hAx := hA x hx
          change dist x 0 ≤ 2*(T+|r|+1)/2
          linarith [abs_nonneg r]
        simp [g,cutoff_one 0 hs hdist]
    have haK : Finsupp.linearCombination ℝ point a ∈ supported K :=
      combination_mem_supported a (fun x hx => Set.mem_insert_of_mem 0 hx)
    have hdiff := pairing_difference_le (show (0 : M) ∈ K from Set.mem_insert _ _) f g hf hg'
      he (μ i) (Finsupp.linearCombination ℝ point a) haK
    have hl := hlarge hf
    norm_num at hdiff
    have habs := le_abs_self (test (normalized f hf) (μ i)-test (normalized g hg') (μ i))
    have habsg := le_abs_self (test (normalized g hg') (μ i))
    linarith

theorem uniform_radius_approx {μ : ℕ → Space M} (hw : WeakSequences.WeakNull μ)
    {ε : ℝ} (hε : 0 < ε) : ∃ R : ℝ, 0 < R ∧
      ∀ i, Approximable (μ i) (Metric.closedBall 0 R) ε := by
  classical
  by_contra h
  have hfail : ∀ R : ℝ, 0 < R → ∃ i, ¬ Approximable (μ i) (Metric.closedBall 0 R) ε := by
    intro R hR
    by_contra! h'
    exact h ⟨R,hR,h'⟩
  choose idx rad g hip hrad hg hg0 hinner houter hlarge using radius_escape_step hε hfail
  let seq : ℕ → ℕ × ℝ := fun n => Nat.rec (0,1) (fun _ q => (idx q.1 q.2,rad q.1 q.2)) n
  have hs (n : ℕ) : seq (n+1) = (idx (seq n).1 (seq n).2,rad (seq n).1 (seq n).2) := rfl
  have hidx : StrictMono (fun n => (seq n).1) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact hip _ _
  have hradius : StrictMono (fun n => (seq n).2) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact hrad _ _
  let tests : ℕ → M → ℝ := fun n => g (seq n).1 (seq n).2
  have htests (n : ℕ) : LipschitzWith 3 (tests n) := hg _ _
  have hd : DisjointTests tests := by
    intro x j k hj hk
    by_contra hjk
    rcases lt_or_gt_of_ne hjk with hjk | hkj
    · have hlow : (seq k).2 < dist x 0 := by
        by_contra hx
        exact hk (hinner _ _ x (le_of_not_gt hx))
      have hupp : dist x 0 < (seq (j+1)).2 := by
        by_contra hx
        exact hj (houter _ _ x (le_of_not_gt hx))
      exact (not_lt_of_ge (hradius.monotone (Nat.succ_le_of_lt hjk))) (hlow.trans hupp)
    · have hlow : (seq j).2 < dist x 0 := by
        by_contra hx
        exact hj (hinner _ _ x (le_of_not_gt hx))
      have hupp : dist x 0 < (seq (k+1)).2 := by
        by_contra hx
        exact hk (houter _ _ x (le_of_not_gt hx))
      exact (not_lt_of_ge (hradius.monotone (Nat.succ_le_of_lt hkj))) (hlow.trans hupp)
  have hw' := hw.subseq (show StrictMono (fun n => (seq (n+1)).1) from
    fun _ _ hnk => hidx (Nat.add_lt_add_right hnk 1))
  have ht := disjoint_tests_vanish hd htests hw'
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht (ε/2) (half_pos hε)
  have hn := hN N le_rfl
  simp only [dist_zero_right,Real.norm_eq_abs] at hn
  exact (not_lt_of_gt (hlarge (seq N).1 (seq N).2 (htests N))) hn

end LipschitzCounterexample.FreeSpace

end

end OAI
