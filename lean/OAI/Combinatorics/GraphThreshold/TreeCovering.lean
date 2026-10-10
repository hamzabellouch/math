import OAI.Combinatorics.GraphThreshold.ProbabilityTreeTrim
import OAI.Combinatorics.GraphThreshold.CapacityIteration
import OAI.Combinatorics.GraphThreshold.AdaptiveTrials
import OAI.Combinatorics.GraphThreshold.TreeReduction
import OAI.Combinatorics.GraphThreshold.BernoulliMonotonicity
import OAI.Combinatorics.GraphThreshold.TreePotential
import Mathlib.Tactic

namespace OAI

/-!
# Covering a probability tree by iterative reductions

Recovery keeps the original and retained path histories distinct, even when
their labels agree. All draws are retained in the accumulating union.
-/

noncomputable section
open Classical

namespace LeanBlast.SecondKahnKalai

/-- A nondecreasing finite list of capacities has a zero prefix followed by
strictly positive capacities. The empty positive suffix is permitted. -/
theorem exists_zero_prefix_positive_suffix (m : ℕ → ℕ) (d : ℕ)
    (hmono : MonotoneOn m (Set.Iio d)) :
    ∃ k, k ≤ d ∧ (∀ i, i < k → m i = 0) ∧
      (∀ i, i < d - k → 0 < m (i + k)) := by
  classical
  by_cases h : ∃ k, k < d ∧ 0 < m k
  · let k := Nat.find h
    have hk : k < d ∧ 0 < m k := Nat.find_spec h
    refine ⟨k, hk.1.le, ?_, ?_⟩
    · intro i hi
      by_contra hzero
      have hip : 0 < m i := Nat.pos_of_ne_zero hzero
      have hki : k ≤ i := Nat.find_min' h ⟨lt_trans hi hk.1, hip⟩
      omega
    · intro i hi
      have hik : i + k < d := by omega
      exact lt_of_lt_of_le hk.2 (hmono hk.1 hik (by omega))
  · refine ⟨d, le_rfl, ?_, ?_⟩
    · intro i hi
      by_contra hzero
      exact h ⟨i, hi, Nat.pos_of_ne_zero hzero⟩
    · intro i hi
      omega

theorem capacityReserve_div_sampling_le {σ : ℝ} (hσ : 0 < σ) (m : ℕ) :
    capacityReserve σ m / (Real.exp 50 * (4 * σ)) ≤ Real.exp (-50) := by
  have hp : 0 < Real.exp 50 * (4 * σ) := by positivity
  calc
    _ ≤ (4 * σ) / (Real.exp 50 * (4 * σ)) :=
      div_le_div_of_nonneg_right (capacityReserve_upper hσ.le m) hp.le
    _ = Real.exp (-50) := by
      rw [Real.exp_neg]
      field_simp

theorem sampling_budget_le {σ : ℝ} (hσ : 0 ≤ σ) (L : ℕ) :
    ((4 * successesNeeded L : ℕ) : ℝ) * (Real.exp 50 * (4 * σ)) ≤
      16 * Real.exp 50 * σ * (1 + Real.logb 2 (L : ℝ)) := by
  calc
    _ = (16 * Real.exp 50 * σ) * (successesNeeded L : ℝ) := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (successesNeeded_le_logb L) (by positivity)

namespace ProbabilityTree

variable {X : Type} [DecidableEq X]

/-- Each path of a retained tree recovers a path of the original tree after
the already collected coordinates are added. -/
def Recovers {d e : ℕ} (T : ProbabilityTree X d) (S : ProbabilityTree X e)
    (W : Finset X) : Prop :=
  ∀ q : S.Path, ∃ p : T.Path, T.pathUnion p ⊆ W ∪ S.pathUnion q

theorem Recovers.refl {d : ℕ} (T : ProbabilityTree X d) : Recovers T T ∅ := by
  intro p
  exact ⟨p, by simp⟩

theorem Recovers.mono {d e : ℕ} {T : ProbabilityTree X d} {S : ProbabilityTree X e}
    {W V : Finset X} (h : Recovers T S W) (hWV : W ⊆ V) : Recovers T S V := by
  intro q
  obtain ⟨p, hp⟩ := h q
  exact ⟨p, hp.trans (Finset.union_subset_union hWV (Finset.Subset.refl _))⟩

/-- Recovery composes through the union of the independent draws. -/
theorem Recovers.trans {d e f : ℕ}
    {T : ProbabilityTree X d} {S : ProbabilityTree X e} {U : ProbabilityTree X f}
    {W V : Finset X} (hTS : Recovers T S W) (hSU : Recovers S U V) :
    Recovers T U (W ∪ V) := by
  intro r
  obtain ⟨q, hq⟩ := hSU r
  obtain ⟨p, hp⟩ := hTS q
  refine ⟨p, ?_⟩
  simpa only [Finset.union_assoc] using
    hp.trans (Finset.union_subset_union (Finset.Subset.refl W) hq)

/-- A covered retained path yields a covered original path. -/
theorem Recovers.coveredBy {d e : ℕ} {T : ProbabilityTree X d} {S : ProbabilityTree X e}
    {W V : Finset X} (h : Recovers T S W) (hS : S.CoveredBy V) :
    T.CoveredBy (W ∪ V) := by
  obtain ⟨q, hq⟩ := hS
  obtain ⟨p, hp⟩ := h q
  exact ⟨p, hp.trans (Finset.union_subset_union (Finset.Subset.refl W) hq)⟩

/-- When no levels remain, recovery is already a covering certificate. -/
theorem Recovers.coveredBy_of_depth_zero {d : ℕ} {T : ProbabilityTree X d}
    {S : ProbabilityTree X 0} {W : Finset X} (h : Recovers T S W) : T.CoveredBy W := by
  cases S
  obtain ⟨p, hp⟩ := h PUnit.unit
  exact ⟨p, by simpa only [pathUnion, Finset.union_empty] using hp⟩

theorem Recovers.coveredBy_of_depth_eq_zero {d e : ℕ} {T : ProbabilityTree X d}
    {S : ProbabilityTree X e} {W : Finset X} (h : Recovers T S W) (he : e = 0) :
    T.CoveredBy W := by
  subst e
  exact h.coveredBy_of_depth_zero

/-- Removing empty initial labels preserves recovery without adding any
coordinates. The path lifting premise is supplied by deterministic prefix
removal. -/
theorem Recovers.of_pathUnion_eq {d e : ℕ}
    {T : ProbabilityTree X d} {S : ProbabilityTree X e}
    (h : ∀ q : S.Path, ∃ p : T.Path, T.pathUnion p = S.pathUnion q) :
    Recovers T S ∅ := by
  intro q
  obtain ⟨p, hp⟩ := h q
  exact ⟨p, by simp [hp]⟩

/-- Increasing each nonnegative level spread parameter preserves spread. -/
theorem HasSpread.mono {d : ℕ} {T : ProbabilityTree X d} {a b : ℕ → ℝ}
    (hT : T.HasSpread a) (ha : ∀ i, i < d → 0 ≤ a i)
    (hab : ∀ i, i < d → a i ≤ b i) : T.HasSpread b := by
  induction T generalizing a b with
  | leaf => trivial
  | @node d B inst law positive label child ih =>
      constructor
      · intro J hJ
        exact (hT.1 J hJ).trans (pow_le_pow_left₀ (ha 0 (by omega)) (hab 0 (by omega)) _)
      · intro c
        exact ih c (hT.2 c) (fun i hi => ha (i + 1) (by omega))
          (fun i hi => hab (i + 1) (by omega))

theorem coveredBy_probability_one [Fintype X] {d : ℕ} (T : ProbabilityTree X d) :
    bernoulliProbability 1 T.CoveredBy = 1 := by
  apply le_antisymm
  · exact (bernoulliLaw 1 (by norm_num) le_rfl).prob_le_one T.CoveredBy
  · have h := (bernoulliLaw (X := X) 1 (by norm_num) le_rfl).prob_mono
      (P := fun W => Finset.univ ⊆ W) (Q := T.CoveredBy)
      (fun _ hW => coveredBy_mono (coveredBy_univ T) hW)
    change bernoulliProbability 1 (fun W => Finset.univ ⊆ W) ≤
      bernoulliProbability 1 T.CoveredBy at h
    simpa only [bernoulliProbability_subset, one_pow] using h

/-- The actual retained tree, its spread budget, and recovery to the fixed
original tree. Only positive-capacity levels are stored. -/
structure CoverState {k : ℕ} (original : ProbabilityTree X k) (σ : ℝ) where
  depth : ℕ
  tree : ProbabilityTree X depth
  capacity : ℕ → ℕ
  disjoint : tree.IsDisjoint
  capacities : tree.HasCapacities capacity
  spread : tree.HasSpread (fun i => capacityReserve σ (capacity i))
  positive : ∀ i, i < depth → 0 < capacity i
  growth : ∀ i, i + 1 < depth → 16 * capacity i ≤ capacity (i + 1)
  seen : Finset X
  recovery : Recovers original tree seen

namespace CoverState

variable {k : ℕ} {original : ProbabilityTree X k} {σ : ℝ}

def initial (original : ProbabilityTree X k) (σ : ℝ) (m : ℕ → ℕ)
    (hσ : 0 < σ) (hdisjoint : original.IsDisjoint)
    (hcapacity : original.HasCapacities m)
    (hspread : original.HasSpread (fun _ => σ))
    (hpositive : ∀ i, i < k → 0 < m i)
    (hgrowth : ∀ i, i + 1 < k → 16 * m i ≤ m (i + 1)) : CoverState original σ :=
  { depth := k
    tree := original
    capacity := m
    disjoint := hdisjoint
    capacities := hcapacity
    spread := hspread.mono (fun _ _ => hσ.le) (fun i _ => capacityReserve_lower hσ.le (m i))
    positive := hpositive
    growth := hgrowth
    seen := ∅
    recovery := Recovers.refl original }

def rank (state : CoverState original σ) : ℕ :=
  if state.depth = 0 then 0 else successesNeeded (state.capacity (state.depth - 1))

@[simp] theorem rank_eq_zero_iff (state : CoverState original σ) :
    state.rank = 0 ↔ state.depth = 0 := by
  unfold rank
  split_ifs with h
  · simp [h]
  · simp [h, ne_of_gt (successesNeeded_pos _)]

theorem coveredBy_of_rank_zero (state : CoverState original σ) (h : state.rank = 0) :
    original.CoveredBy state.seen :=
  state.recovery.coveredBy_of_depth_eq_zero ((rank_eq_zero_iff state).mp h)

/-- Every draw is retained even when the reduction attempt fails. -/
def accumulate (state : CoverState original σ) (W : Finset X) : CoverState original σ :=
  { state with
    seen := state.seen ∪ W
    recovery := state.recovery.mono Finset.subset_union_left }

@[simp] theorem accumulate_rank (state : CoverState original σ) (W : Finset X) :
    (state.accumulate W).rank = state.rank := rfl

def Advances (state : CoverState original σ) (W : Finset X)
    (next : CoverState original σ) : Prop :=
  next.rank < state.rank ∧ next.seen = state.seen ∪ W

/-- Choose a strict improvement when one exists; otherwise keep the tree.
Existence of improvements will be supplied by the actual good-tree reduction. -/
def step (state : CoverState original σ) (W : Finset X) : CoverState original σ :=
  if h : ∃ next, state.Advances W next then Classical.choose h else state.accumulate W

theorem step_seen (state : CoverState original σ) (W : Finset X) :
    (state.step W).seen = state.seen ∪ W := by
  unfold step
  split_ifs with h
  · exact (Classical.choose_spec h).2
  · rfl

theorem step_rank_le (state : CoverState original σ) (W : Finset X) :
    (state.step W).rank ≤ state.rank := by
  unfold step
  split_ifs with h
  · exact (Classical.choose_spec h).1.le
  · exact le_rfl

theorem step_rank_lt_of_exists (state : CoverState original σ) (W : Finset X)
    (h : ∃ next, state.Advances W next) : (state.step W).rank < state.rank := by
  unfold step
  rw [dite_eq_left h]
  exact (Classical.choose_spec h).1

theorem biUnion_fin_succ {n : ℕ} (draws : Fin (n + 1) → Finset X) :
    Finset.univ.biUnion draws = draws 0 ∪ Finset.univ.biUnion (fun i : Fin n => draws i.succ) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    refine Fin.cases (fun hx => Or.inl hx) (fun j hx => Or.inr ⟨j, hx⟩) i hi
  · rintro (h | ⟨i, hi⟩)
    · exact ⟨0, h⟩
    · exact ⟨i.succ, hi⟩

/-- The recorded set is exactly the union of all draws, including failures. -/
theorem run_seen (n : ℕ) (state : CoverState original σ) (draws : Fin n → Finset X) :
    (adaptiveRun step n state draws).seen = state.seen ∪ Finset.univ.biUnion draws := by
  induction n generalizing state with
  | zero => simp [adaptiveRun]
  | succ n ih =>
      rw [adaptiveRun, ih, step_seen, biUnion_fin_succ, Finset.union_assoc]

/-- The finite adaptive theorem transfers actual strict advances to covering.
The good-tree probability estimate supplies the premise in the final theorem. -/
theorem prob_covered_of_advance_probability [Fintype X] (μ : FiniteLaw (Finset X))
    (hprogress : ∀ state : CoverState original σ, state.rank ≠ 0 →
      (3 / 4 : ℝ) ≤ μ.prob (fun W => ∃ next, state.Advances W next))
    (s : ℕ) (state : CoverState original σ) (hrank : state.rank ≤ s) :
    (2 / 3 : ℝ) ≤ (μ.iid (4 * s)).prob
      (fun draws => original.CoveredBy (state.seen ∪ Finset.univ.biUnion draws)) := by
  have hp : ∀ st : CoverState original σ, st.rank ≠ 0 →
      (3 / 4 : ℝ) ≤ μ.prob (fun W => (st.step W).rank < st.rank) := by
    intro st hst
    exact (hprogress st hst).trans (μ.prob_mono fun W hW => st.step_rank_lt_of_exists W hW)
  have hcomplete := adaptive_rank_completion μ rank step step_rank_le hp s state hrank
  apply hcomplete.trans
  apply (μ.iid (4 * s)).prob_mono
  intro draws hdraws
  have hcover := (adaptiveRun step (4 * s) state draws).coveredBy_of_rank_zero hdraws
  rwa [run_seen] at hcover

/-- A halved tree, after its zero prefix is removed, is a strict improvement
of the current positive-capacity tree. -/
theorem exists_advance_of_halved (state : CoverState original σ) (W : Finset X)
    (hdepth : state.depth ≠ 0) (U : ProbabilityTree X state.depth)
    (hdisjoint : U.IsDisjoint)
    (hcapacity : U.HasCapacities (fun i => state.capacity i / 2))
    (hspread : U.HasSpread (fun i => capacityReserve σ (state.capacity i / 2)))
    (hrecovery : Recovers state.tree U W) :
    ∃ next, state.Advances W next := by
  let m : ℕ → ℕ := fun i => state.capacity i / 2
  have hgrowth : ∀ i, i + 1 < state.depth → 16 * m i ≤ m (i + 1) := by
    intro i hi
    simpa [m, reducedCapacity] using reducedCapacity_growth (state.growth i hi) 1
  obtain ⟨j, hj, hzero, hpositive⟩ := exists_zero_prefix_positive_suffix m state.depth
    (monotoneOn_capacities m state.depth hgrowth)
  let V := U.dropPrefix j hj
  have htrim : Recovers U V ∅ := by
    apply Recovers.of_pathUnion_eq
    intro q
    exact ⟨liftDropPrefixPath U j hj q,
      pathUnion_liftDropPrefixPath_eq hcapacity j hj hzero q⟩
  let next : CoverState original σ :=
    { depth := state.depth - j
      tree := V
      capacity := fun i => m (i + j)
      disjoint := dropPrefix_isDisjoint hdisjoint j hj
      capacities := dropPrefix_hasCapacities hcapacity j hj
      spread := dropPrefix_hasSpread hspread j hj
      positive := hpositive
      growth := by
        intro i hi
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hgrowth (i + j) (by omega)
      seen := state.seen ∪ W
      recovery := by
        simpa only [Finset.union_empty] using (state.recovery.trans hrecovery).trans htrim }
  refine ⟨next, ?_, rfl⟩
  change (if state.depth - j = 0 then 0 else
    successesNeeded (m (state.depth - j - 1 + j))) < state.rank
  by_cases hempty : state.depth - j = 0
  · rw [ite_eq_left hempty]
    exact Nat.pos_of_ne_zero (fun h => hdepth ((rank_eq_zero_iff state).mp h))
  · rw [ite_eq_right hempty]
    have hindex : state.depth - j - 1 + j = state.depth - 1 := by omega
    rw [hindex]
    unfold rank
    rw [ite_eq_right hdepth]
    apply successesNeeded_half_lt
    have hp := hpositive (state.depth - j - 1) (by omega)
    simpa only [hindex] using hp

/-- A good draw produces an actual strict advance: construct the pruned tree,
preserve the reserve budget, and delete exactly its zero-capacity prefix. -/
theorem exists_advance_of_good (state : CoverState original σ) (W : Finset X)
    (hσ : 0 < σ) {ρ : ℝ} (hρ : 0 < ρ) (hrank : state.rank ≠ 0)
    (hgood : Good ρ state.capacity W state.tree) :
    ∃ next, state.Advances W next := by
  let U := reduceTree ρ state.capacity W state.tree hρ state.positive hgood
  have ha : ∀ i, i < state.depth → 0 ≤ capacityReserve σ (state.capacity i) :=
    fun i _ => (capacityReserve_pos hσ (state.capacity i)).le
  have hspread := reduceTree_hasSpread ρ state.capacity W state.tree hρ state.positive
    hgood (fun i => capacityReserve σ (state.capacity i)) ha state.spread
  refine state.exists_advance_of_halved W
    (fun hd => hrank ((rank_eq_zero_iff state).mpr hd)) U
    (reduceTree_isDisjoint ρ state.capacity W state.tree hρ state.positive hgood state.disjoint)
    (reduceTree_hasCapacities ρ state.capacity W state.tree hρ state.positive hgood) ?_
    (reduceTree_path_recovery ρ state.capacity W state.tree hρ state.positive hgood)
  exact hspread.mono
    (fun i hi => div_nonneg (ha i hi) (retentionFactor_pos (state.positive i hi)).le)
    (fun i hi => capacityReserve_div_le_half hσ.le (state.positive i hi))

end CoverState

end ProbabilityTree

/-- The finite random experiment and final parameter comparison. The next
theorem supplies this private lemma's progress estimate from actual reduction. -/
private theorem tree_covering_of_progress {X : Type} [Fintype X] [DecidableEq X]
    {k : ℕ} (T : ProbabilityTree X k) (hk : 0 < k) (hdis : T.IsDisjoint)
    (m : ℕ → ℕ) (hcap : T.HasCapacities m) (hpos : ∀ i, i < k → 0 < m i)
    (hgrowth : ∀ i, i + 1 < k → 16 * m i ≤ m (i + 1))
    (σ : ℝ) (hσ : 0 < σ) (hspread : T.HasSpread (fun _ => σ))
    (hprogress : Real.exp 50 * (4 * σ) < 1 →
      ∀ state : ProbabilityTree.CoverState T σ, state.rank ≠ 0 →
        (3 / 4 : ℝ) ≤ bernoulliProbability (Real.exp 50 * (4 * σ))
          (fun W => ∃ next, state.Advances W next)) :
    (2 / 3 : ℝ) ≤ bernoulliProbability
      (min 1 (16 * Real.exp 50 * σ * (1 + Real.logb 2 (m (k - 1) : ℝ)))) T.CoveredBy := by
  let B := 16 * Real.exp 50 * σ * (1 + Real.logb 2 (m (k - 1) : ℝ))
  change (2 / 3 : ℝ) ≤ bernoulliProbability (min 1 B) T.CoveredBy
  by_cases hB : 1 ≤ B
  · rw [min_eq_left hB, ProbabilityTree.coveredBy_probability_one]
    norm_num
  have hB1 : B < 1 := lt_of_not_ge hB
  let p := Real.exp 50 * (4 * σ)
  have hp : 0 < p := by dsimp [p]; positivity
  have hlog : 0 ≤ Real.logb 2 (m (k - 1) : ℝ) :=
    capacity_logb_nonneg (hpos (k - 1) (by omega))
  have hBp : 4 * p ≤ B := by
    calc
      4 * p = (16 * Real.exp 50 * σ) * 1 := by dsimp [p]; ring
      _ ≤ B := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤
        1 + Real.logb 2 (m (k - 1) : ℝ)) (by positivity)
  have hp1 : p < 1 := by linarith
  let μ := bernoulliLaw (X := X) p hp.le hp1.le
  let state := ProbabilityTree.CoverState.initial T σ m hσ hdis hcap hspread hpos hgrowth
  let s := successesNeeded (m (k - 1))
  have hrank : state.rank ≤ s := by
    change (if k = 0 then 0 else successesNeeded (m (k - 1))) ≤ s
    rw [ite_eq_right (Nat.ne_of_gt hk)]
  have hprog : ∀ st : ProbabilityTree.CoverState T σ, st.rank ≠ 0 →
      (3 / 4 : ℝ) ≤ μ.prob (fun W => ∃ next, st.Advances W next) :=
    fun st hst => hprogress hp1 st hst
  have hc := ProbabilityTree.CoverState.prob_covered_of_advance_probability μ hprog s state hrank
  have hseen : state.seen = ∅ := rfl
  simp only [hseen, Finset.empty_union] at hc
  change (2 / 3 : ℝ) ≤ ((bernoulliLaw p hp.le hp1.le).iid (4 * s)).prob
    (fun draws => T.CoveredBy (Finset.univ.biUnion draws)) at hc
  rw [iid_bernoulli_union_probability] at hc
  have hq0 := (bernoulli_union_parameter_mem hp.le hp1.le (4 * s)).1
  have hqB : 1 - (1 - p) ^ (4 * s) ≤ B :=
    (bernoulli_union_parameter_le hp.le hp1.le (4 * s)).trans
      (sampling_budget_le hσ.le (m (k - 1)))
  have hmono := bernoulliProbability_mono_parameter hq0 hqB hB1.le T.CoveredBy
    (fun _ _ hUV hU => ProbabilityTree.coveredBy_mono hU hUV)
  rw [min_eq_right hB1.le]
  exact hc.trans hmono

theorem tree_covering {X : Type} [Fintype X] [DecidableEq X] {k : ℕ}
    (T : ProbabilityTree X k) (hk : 0 < k) (hdis : T.IsDisjoint)
    (m : ℕ → ℕ) (hcap : T.HasCapacities m) (hpos : ∀ i, i < k → 0 < m i)
    (hgrowth : ∀ i, i + 1 < k → 16 * m i ≤ m (i + 1))
    (σ : ℝ) (hσ : 0 < σ) (hspread : T.HasSpread (fun _ => σ)) :
    (2 / 3 : ℝ) ≤ bernoulliProbability
      (min 1 (16 * Real.exp 50 * σ * (1 + Real.logb 2 (m (k - 1) : ℝ)))) T.CoveredBy := by
  apply tree_covering_of_progress T hk hdis m hcap hpos hgrowth σ hσ hspread
  intro hp1 state hrank
  have hp : 0 < Real.exp 50 * (4 * σ) := by positivity
  have hgood := reduction_good_probability_ge hp hp1 state.capacity
    (fun i => capacityReserve σ (state.capacity i)) state.tree
    state.disjoint state.capacities state.spread state.positive
    (fun i _ => (capacityReserve_pos hσ (state.capacity i)).le)
    (fun i _ => capacityReserve_div_sampling_le hσ (state.capacity i)) state.growth
  have hmono := (bernoulliLaw (X := X) (Real.exp 50 * (4 * σ)) hp.le hp1.le).prob_mono
    (P := fun W => Good (Real.exp 50 * (4 * σ)) state.capacity W state.tree)
    (Q := fun W => ∃ next, state.Advances W next)
    (fun W hW => state.exists_advance_of_good W hσ hp hrank hW)
  exact hgood.trans hmono

end LeanBlast.SecondKahnKalai

end

end OAI
