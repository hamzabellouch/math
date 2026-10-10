import OAI.Analysis.LipschitzEquivalence.CauchyApproximation

namespace OAI

universe uM uE

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

structure CauchyLocalizationState (R : ℝ≥0) where
  seq : ℕ → Space M
  weak : WeakSequences.WeakCauchy seq
  set : Set M
  closed : IsClosed set
  zero_mem : (0 : M) ∈ set
  bounded : set ⊆ Metric.closedBall 0 (R : ℝ)
  support : ∀ i, seq i ∈ supported set

theorem cauchy_localization_step {R : ℝ≥0} (W : CauchyLocalizationState (M := M) R)
    {δ : ℝ≥0} (hδ : 0 < δ) {η : ℝ} (hη : 0 < η) :
    ∃ V : CauchyLocalizationState (M := M) R, V.set ⊆ W.set ∧
      (∃ A : Finset M, V.set ⊆ Near A (2*δ)) ∧
      ∀ i, dist (W.seq i) (V.seq i) < η := by
  have hsupp (i : ℕ) : W.seq i ∈ supported (Metric.closedBall 0 (R : ℝ)) :=
    supported_mono W.bounded (W.support i)
  let C : ℝ := 4+finiteMultiplierBound R δ
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨A,hA,happrox⟩ := uniform_finite_neighborhood_approx_cauchy W.weak hsupp hδ (div_pos hη hC)
  let V : CauchyLocalizationState (M := M) R := {
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

theorem bounded_cauchy_compact_reduction [CompleteSpace M] {R : ℝ≥0} {μ : ℕ → Space M}
    (hw : WeakSequences.WeakCauchy μ)
    (hsupp : ∀ i, μ i ∈ supported (Metric.closedBall 0 (R : ℝ)))
    {τ : ℝ} (hτ : 0 < τ) : ∃ K : Set M, IsCompact K ∧ (0 : M) ∈ K ∧
      ∃ ν : ℕ → Space M, WeakSequences.WeakCauchy ν ∧
        (∀ i, ν i ∈ supported K) ∧ ∀ i, ‖μ i-ν i‖ < τ := by
  classical
  let δ : ℕ → ℝ≥0 := fun n => (1/2)^n
  let η : ℕ → ℝ := fun n => (τ/4)*(1/2)^n
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hη (n : ℕ) : 0 < η n := by dsimp [η]; positivity
  choose next hsub hcover herr using fun n (W : CauchyLocalizationState (M := M) R) =>
    cauchy_localization_step W (hδ n) (hη n)
  let start : CauchyLocalizationState (M := M) R := {
    seq := μ
    weak := hw
    set := Metric.closedBall 0 (R : ℝ)
    closed := Metric.isClosed_closedBall
    zero_mem := by simp
    bounded := Set.Subset.rfl
    support := hsupp }
  let W : ℕ → CauchyLocalizationState (M := M) R := fun n =>
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
  have hstep (i n : ℕ) : dist ((W n).seq i) ((W (n+1)).seq i) ≤ (τ/4)*(1/2)^n :=
    (herr n (W n) i).le
  choose ν hν using fun i => cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1/2) (τ/4) (by norm_num) (hstep i))
  have hdist (i n : ℕ) : ‖(W n).seq i-ν i‖ ≤ (τ/2)*(1/2)^n := by
    have hh := dist_le_of_le_geometric_of_tendsto (1/2) (τ/4) (by norm_num)
      (hstep i) (hν i) n
    rw [dist_eq_norm] at hh
    convert hh using 1; ring
  have hwν : WeakSequences.WeakCauchy ν := by
    apply WeakSequences.weakCauchy_of_uniform_approx
    intro ε hε
    have hlim : Tendsto (fun n => (τ/2)*(1/2 : ℝ)^n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ) < 1)).const_mul (τ/2)
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
    refine ⟨(W N).seq,(W N).weak,fun i => ?_⟩
    rw [norm_sub_rev]
    exact (hdist i N).trans_lt (hN N le_rfl)
  refine ⟨⋂ n, K n,hcompact,Set.mem_iInter.mpr (fun n => (W n).zero_mem),
    ν,hwν,fun i => ?_,fun i => ?_⟩
  · apply supported_intersection_of_uniform K huniform
    intro n
    apply (supported_isClosed (K n)).mem_of_tendsto (hν i)
    filter_upwards [eventually_ge_atTop n] with m hm
    exact supported_mono (hanti hm) ((W m).support i)
  · have hh := hdist i 0
    change ‖μ i-ν i‖ ≤ _ at hh
    simp only [pow_zero,mul_one] at hh
    exact hh.trans_lt (by linarith)

theorem cauchy_compact_reduction [CompleteSpace M] {μ : ℕ → Space M}
    (hw : WeakSequences.WeakCauchy μ) {τ : ℝ} (hτ : 0 < τ) :
    ∃ K : Set M, IsCompact K ∧ (0 : M) ∈ K ∧
      ∃ ν : ℕ → Space M, WeakSequences.WeakCauchy ν ∧
        (∀ i, ν i ∈ supported K) ∧ ∀ i, ‖μ i-ν i‖ < τ := by
  obtain ⟨R,v,hv,hsupp,herr⟩ := bounded_cauchy_approx hw (half_pos hτ)
  obtain ⟨K,hK,hzero,ν,hν,hmem,happrox⟩ :=
    bounded_cauchy_compact_reduction hv hsupp (half_pos hτ)
  refine ⟨K,hK,hzero,ν,hν,hmem,fun i => ?_⟩
  have h : ‖μ i-ν i‖ ≤ ‖μ i-v i‖+‖v i-ν i‖ := by
    rw [show μ i-ν i = (μ i-v i)+(v i-ν i) by abel]
    exact norm_add_le _ _
  have h₁ := herr i
  have h₂ := happrox i
  linarith

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.WeakSequences
open Filter Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weakCauchy_biddual_limit {u : ℕ → E} (hu : WeakCauchy u) :
    ∃ φ : (E →L[ℝ] ℝ) →L[ℝ] ℝ,
      ∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (φ f)) := by
  classical
  choose a ha using fun f : E →L[ℝ] ℝ => cauchySeq_tendsto_of_complete (hu f)
  let L : (E →L[ℝ] ℝ) →ₗ[ℝ] ℝ := {
    toFun := a
    map_add' := fun f g => tendsto_nhds_unique (ha (f+g)) ((ha f).add (ha g))
    map_smul' := fun c f => tendsto_nhds_unique (ha (c • f)) ((ha f).const_smul c) }
  obtain ⟨C,hC⟩ := hu.bounded
  have hbound (f : E →L[ℝ] ℝ) : ‖L f‖ ≤ C*‖f‖ := by
    apply le_of_tendsto (ha f).norm
    apply Eventually.of_forall
    intro n
    exact (f.le_opNorm (u n)).trans (by nlinarith [norm_nonneg f,hC n])
  exact ⟨L.mkContinuous C hbound,ha⟩

theorem wsc_of_uniform_weak_approx [CompleteSpace E] {u : ℕ → E} (hu : WeakCauchy u)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ v : ℕ → E, ∃ x : E,
      (∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (v n)) atTop (𝓝 (f x))) ∧
      ∀ n, ‖u n-v n‖ < ε) :
    ∃ x : E, ∀ f : E →L[ℝ] ℝ, Tendsto (fun n => f (u n)) atTop (𝓝 (f x)) := by
  obtain ⟨φ,hφ⟩ := weakCauchy_biddual_limit hu
  let I : E →ₗᵢ[ℝ] ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
    NormedSpace.inclusionInDoubleDualLi (E := E) ℝ
  have hmem : φ ∈ closure (Set.range I) := by
    rw [@Metric.mem_closure_iff ((E →L[ℝ] ℝ) →L[ℝ] ℝ) inferInstance]
    intro ε hε
    obtain ⟨v,x,hx,herr⟩ := happrox (ε/2) (half_pos hε)
    refine ⟨I x,⟨x,rfl⟩,?_⟩
    have hnorm : ‖φ-I x‖ ≤ ε/2 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le
      intro f
      change ‖φ f-f x‖ ≤ (ε/2)*‖f‖
      apply le_of_tendsto ((hφ f).sub (hx f)).norm
      apply Eventually.of_forall
      intro n
      rw [← map_sub]
      exact (f.le_opNorm _).trans (by nlinarith [norm_nonneg f,herr n])
    rw [show dist φ (I x) = ‖φ-I x‖ from
      @dist_eq_norm ((E →L[ℝ] ℝ) →L[ℝ] ℝ) inferInstance φ (I x)]
    exact hnorm.trans_lt (by linarith)
  have hI : Isometry (I : E → ((E →L[ℝ] ℝ) →L[ℝ] ℝ)) := I.isometry
  have hclosed : IsClosed (Set.range I) := hI.isClosedEmbedding.isClosed_range
  rw [hclosed.closure_eq] at hmem
  obtain ⟨x,hx⟩ := hmem
  refine ⟨x,fun f => ?_⟩
  simpa [← hx, I, NormedSpace.inclusionInDoubleDualLi, NormedSpace.inclusionInDoubleDual] using hφ f

end LipschitzCounterexample.WeakSequences

namespace LipschitzCounterexample.FreeSpace
open Filter Topology
variable {M : Type uM} [MetricSpace M] [Zero M] [CompleteSpace M]

theorem wsc_of_compact_supported
    (hcompact : ∀ K : Set M, IsCompact K → (0 : M) ∈ K →
      WeakSequences.WeakSequentiallyComplete (supported K)) :
    WeakSequences.WeakSequentiallyComplete (Space M) := by
  intro μ hμ
  apply WeakSequences.wsc_of_uniform_weak_approx hμ
  intro ε hε
  obtain ⟨K,hK,hzero,ν,hν,hmem,herr⟩ := cauchy_compact_reduction hμ hε
  let v : ℕ → supported K := fun n => ⟨ν n,hmem n⟩
  have hv : WeakSequences.WeakCauchy v := by
    intro f
    obtain ⟨g,hg,_⟩ := exists_extension_norm_eq (supported K) f
    simpa only [← hg] using hν g
  obtain ⟨x,hx⟩ := hcompact K hK hzero v hv
  refine ⟨ν,(x : Space M),fun f => ?_,herr⟩
  exact hx (f.comp (supported K).subtypeL)

end LipschitzCounterexample.FreeSpace

end

end OAI
