import OAI.Analysis.LipschitzEquivalence.WeakCauchy

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

theorem uniform_radius_approx_cauchy {μ : ℕ → Space M} (hw : WeakSequences.WeakCauchy μ)
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
  have ht := disjoint_tests_vanish_cauchy hd htests hw'
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht (ε/2) (half_pos hε)
  have hn := hN N le_rfl
  simp only [dist_zero_right,Real.norm_eq_abs] at hn
  exact (not_lt_of_gt (hlarge (seq N).1 (seq N).2 (htests N))) hn

theorem uniform_finite_neighborhood_approx_cauchy {μ : ℕ → Space M}
    (hw : WeakSequences.WeakCauchy μ) {R : ℝ≥0}
    (hsupp : ∀ i, μ i ∈ supported (Metric.closedBall 0 (R : ℝ)))
    {δ : ℝ≥0} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset M, (0 : M) ∈ A ∧ ∀ i, Approximable (μ i) (Near A δ) ε := by
  classical
  by_contra h
  have hfail : ∀ A : Finset M, (0 : M) ∈ A → ∃ i, ¬ Approximable (μ i) (Near A δ) ε := by
    intro A hA
    by_contra! h'
    exact h ⟨A,hA,h'⟩
  choose idx pts tests hip hpts hequi hz hinner houter hlarge using
    finite_escape_step hε hsupp hδ hfail
  let seq : ℕ → ℕ × Finset M := fun n =>
    Nat.rec (0,{0}) (fun _ q => (idx q.1 q.2,q.2 ∪ pts q.1 q.2)) n
  have hidx : StrictMono (fun n => (seq n).1) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact hip _ _
  have hsets : Monotone (fun n => (seq n).2) := by
    apply monotone_nat_of_le_succ
    intro n
    exact Finset.subset_union_left
  let g : ℕ → M → ℝ := fun n => tests (seq n).1 (seq n).2
  have hg (n : ℕ) : LipschitzWith (3+(2/δ)*(2*R+2)) (g n) := hequi _ _
  have hexcl (j k : ℕ) (hjk : j < k) (x : M) (hj : g j x ≠ 0) : g k x = 0 := by
    have hx := houter (seq j).1 (seq j).2 x hj
    apply hinner
    apply near_mono (hsets (Nat.succ_le_of_lt hjk)) _
    exact near_mono Finset.subset_union_right _ hx
  have hd : DisjointTests g := by
    intro x j k hj hk
    by_contra hjk
    rcases lt_or_gt_of_ne hjk with hjk | hkj
    · exact hk (hexcl j k hjk x hj)
    · exact hj (hexcl k j hkj x hk)
  have hw' := hw.subseq (show StrictMono (fun n => (seq (n+1)).1) from
    fun _ _ hnk => hidx (Nat.add_lt_add_right hnk 1))
  have ht := disjoint_tests_vanish_cauchy hd hg hw'
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht (ε/2) (half_pos hε)
  have hn := hN N le_rfl
  simp only [dist_zero_right,Real.norm_eq_abs] at hn
  exact (not_lt_of_gt (hlarge (seq N).1 (seq N).2 (hg N))) hn

theorem bounded_cauchy_approx {μ : ℕ → Space M} (hw : WeakSequences.WeakCauchy μ)
    {ε : ℝ} (hε : 0 < ε) : ∃ R : ℝ≥0, ∃ v : ℕ → Space M,
      WeakSequences.WeakCauchy v ∧ (∀ i, v i ∈ supported (Metric.closedBall 0 (R : ℝ))) ∧
      ∀ i, ‖μ i-v i‖ < ε := by
  obtain ⟨r,hr,happrox⟩ := uniform_radius_approx_cauchy hw (show 0 < ε/8 by positivity)
  let R : ℝ≥0 := ⟨r,hr.le⟩
  let T : Space M →L[ℝ] Space M := radialMultiplier R
  refine ⟨outerRadius R,(fun i => T (μ i)),hw.map T,fun i => radialMultiplier_supported R (μ i),?_⟩
  intro i
  obtain ⟨ν,hν,herr⟩ := happrox i
  have he : (ContinuousLinearMap.id ℝ (Space M)) ν = T ν := (radialMultiplier_identity R hν).symm
  have hbound := norm_sub_apply_le_of_agree (ContinuousLinearMap.id ℝ (Space M)) T (μ i) ν he
  have hT := norm_radialMultiplier_le (M := M) R
  have hid := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Space M)
  have hn := norm_nonneg (μ i-ν)
  change ‖μ i-T (μ i)‖ ≤ _ at hbound
  have hc : ‖ContinuousLinearMap.id ℝ (Space M)‖+‖T‖ ≤ 4 := by dsimp [T]; linarith
  exact (hbound.trans (mul_le_mul_of_nonneg_right hc hn)).trans_lt (by linarith)

end LipschitzCounterexample.FreeSpace

end

end OAI
