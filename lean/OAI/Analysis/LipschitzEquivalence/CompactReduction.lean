import OAI.Analysis.LipschitzEquivalence.CompactSupports

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

structure LocalizationState (R : ℝ≥0) where
  seq : ℕ → Space M
  weak : WeakSequences.WeakNull seq
  set : Set M
  closed : IsClosed set
  zero_mem : (0 : M) ∈ set
  bounded : set ⊆ Metric.closedBall 0 (R : ℝ)
  support : ∀ i, seq i ∈ supported set

theorem localization_step {R : ℝ≥0} (W : LocalizationState (M := M) R)
    {δ : ℝ≥0} (hδ : 0 < δ) {η : ℝ} (hη : 0 < η) :
    ∃ V : LocalizationState (M := M) R, V.set ⊆ W.set ∧
      (∃ A : Finset M, V.set ⊆ Near A (2*δ)) ∧
      ∀ i, dist (W.seq i) (V.seq i) < η := by
  have hsupp (i : ℕ) : W.seq i ∈ supported (Metric.closedBall 0 (R : ℝ)) :=
    supported_mono W.bounded (W.support i)
  let C : ℝ := 4+finiteMultiplierBound R δ
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨A,hA,happrox⟩ := uniform_finite_neighborhood_approx W.weak hsupp hδ (div_pos hη hC)
  let V : LocalizationState (M := M) R := {
    seq := fun i => finiteMultiplier R A δ (W.seq i)
    weak := W.weak.map (finiteMultiplier R A δ)
    set := W.set ∩ Near A (2*δ)
    closed := W.closed.inter (near_isClosed A _)
    zero_mem := ⟨W.zero_mem,0,hA,by simp⟩
    bounded := fun _ hx => W.bounded hx.1
    support := fun i => finiteMultiplier_support R A hA hδ (W.support i) }
  refine ⟨V,Set.inter_subset_left,⟨A,Set.inter_subset_right⟩,?_⟩
  intro i
  obtain ⟨ν,hν,herr⟩ := happrox i
  have h := finiteMultiplier_error R A hδ (hsupp i) hν
  have hmul := (mul_lt_mul_of_pos_left herr hC)
  rw [mul_div_cancel₀ _ (ne_of_gt hC)] at hmul
  change dist (W.seq i) (finiteMultiplier R A δ (W.seq i)) < η
  rw [dist_eq_norm]
  have hh : (3+(finiteMultiplierBound R δ : ℝ))*‖W.seq i-ν‖ ≤ C*‖W.seq i-ν‖ := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    dsimp [C]; linarith
  exact (h.trans hh).trans_lt hmul

theorem bounded_compact_reduction [CompleteSpace M] {R : ℝ≥0} {μ : ℕ → Space M}
    (hw : WeakSequences.WeakNull μ)
    (hsupp : ∀ i, μ i ∈ supported (Metric.closedBall 0 (R : ℝ)))
    {τ : ℝ} (hτ : 0 < τ) : ∃ K : Set M, IsCompact K ∧ (0 : M) ∈ K ∧
      ∀ i, ∃ ν : Space M, ν ∈ supported K ∧ ‖μ i-ν‖ < τ := by
  classical
  let δ : ℕ → ℝ≥0 := fun n => (1/2)^n
  let η : ℕ → ℝ := fun n => (τ/4)*(1/2)^n
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hη (n : ℕ) : 0 < η n := by dsimp [η]; positivity
  choose next hsub hcover herr using fun n (W : LocalizationState (M := M) R) =>
    localization_step W (hδ n) (hη n)
  let start : LocalizationState (M := M) R := {
    seq := μ
    weak := hw
    set := Metric.closedBall 0 (R : ℝ)
    closed := Metric.isClosed_closedBall
    zero_mem := by simp
    bounded := Set.Subset.rfl
    support := hsupp }
  let W : ℕ → LocalizationState (M := M) R := fun n =>
    Nat.rec start (fun n V => next n V) n
  have hsucc (n : ℕ) : W (n+1) = next n (W n) := rfl
  let K : ℕ → Set M := fun n => (W n).set
  have hanti : Antitone K := by
    apply antitone_nat_of_succ_le
    intro n
    exact hsub n (W n)
  choose A hA using fun n => hcover n (W n)
  have hcov (n : ℕ) : K (n+1) ⊆ Near (A n) (2*(δ n : ℝ)) := hA n
  have hr : Tendsto (fun n => 2*(δ n : ℝ)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => (1/2 : ℝ)^n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [δ] using hlim.const_mul 2
  have hc (n : ℕ) : IsClosed (K n) := (W n).closed
  have hcompact := nested_finite_cover_compact K hc A _ hr hcov
  have huniform := fun (ε : ℝ) (hε : 0 < ε) =>
    nested_finite_cover_uniform K hc hanti A _ hr hcov hε
  refine ⟨⋂ n, K n,hcompact,Set.mem_iInter.mpr (fun n => (W n).zero_mem),?_⟩
  intro i
  have hstep (n : ℕ) : dist ((W n).seq i) ((W (n+1)).seq i) ≤ (τ/4)*(1/2)^n :=
    (herr n (W n) i).le
  obtain ⟨ν,hν⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1/2) (τ/4) (by norm_num) hstep)
  have hmem (n : ℕ) : ν ∈ supported (K n) := by
    apply (supported_isClosed (K n)).mem_of_tendsto hν
    filter_upwards [eventually_ge_atTop n] with m hm
    exact supported_mono (hanti hm) ((W m).support i)
  refine ⟨ν,supported_intersection_of_uniform K huniform ν hmem,?_⟩
  have hdist := dist_le_of_le_geometric_of_tendsto₀ (1/2) (τ/4) (by norm_num) hstep hν
  change dist (μ i) ν ≤ _ at hdist
  rw [dist_eq_norm] at hdist
  have he : τ/4/(1-1/2 : ℝ) = τ/2 := by ring
  rw [he] at hdist
  exact hdist.trans_lt (by linarith)

theorem hasCompactReduction [CompleteSpace M] :
    ∀ μ : ℕ → Space M, WeakSequences.WeakNull μ → ∀ τ : ℝ, 0 < τ →
      ∃ K : Set M, IsCompact K ∧ (0 : M) ∈ K ∧
        ∀ i, ∃ ν : Space M, ν ∈ supported K ∧ ‖μ i-ν‖ < τ := by
  intro μ hw τ hτ
  obtain ⟨R,v,hv,hsupp,herr⟩ := bounded_weak_approx hw (half_pos hτ)
  obtain ⟨K,hK,hzero,happrox⟩ := bounded_compact_reduction hv hsupp (half_pos hτ)
  refine ⟨K,hK,hzero,fun i => ?_⟩
  obtain ⟨ν,hν,hνerr⟩ := happrox i
  refine ⟨ν,hν,?_⟩
  have h : ‖μ i-ν‖ ≤ ‖μ i-v i‖+‖v i-ν‖ := by
    rw [show μ i-ν = (μ i-v i)+(v i-ν) by abel]
    exact norm_add_le _ _
  have h₁ := herr i
  linarith

end LipschitzCounterexample.FreeSpace

end

end OAI
