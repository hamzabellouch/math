import OAI.Combinatorics.Ryser.Selection.Chunk
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

section FiniteSets

variable {ι ε β : Type*} [DecidableEq β]

theorem card_le_card_sdiff_biUnion_add_sum_card_inter
    (U : Finset β) (E : Finset ε) (L : ε → Finset β) :
    U.card ≤ (U \ E.biUnion L).card + ∑ e ∈ E, (U ∩ L e).card := by
  have hpartition := Finset.card_sdiff_add_card_inter U (E.biUnion L)
  have hcover : (U ∩ E.biUnion L).card ≤ ∑ e ∈ E, (U ∩ L e).card := by
    rw [Finset.inter_biUnion]
    exact Finset.card_biUnion_le
  omega

theorem sum_card_le_sum_card_sdiff_biUnion_add_sum_card_inter
    (I : Finset ι) (U : ι → Finset β) (E : Finset ε)
    (L : ε → ι → Finset β) :
    (∑ i ∈ I, (U i).card) ≤
      (∑ i ∈ I, (U i \ E.biUnion (fun e => L e i)).card) +
        ∑ e ∈ E, ∑ i ∈ I, (U i ∩ L e i).card := by
  calc
    (∑ i ∈ I, (U i).card) ≤
        ∑ i ∈ I, ((U i \ E.biUnion (fun e => L e i)).card +
          ∑ e ∈ E, (U i ∩ L e i).card) := by
      exact Finset.sum_le_sum fun i _ =>
        card_le_card_sdiff_biUnion_add_sum_card_inter (U i) E (fun e => L e i)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_comm]

theorem sum_card_sub_sum_card_sdiff_biUnion_le_nat
    (I : Finset ι) (U : ι → Finset β) (E : Finset ε)
    (L : ε → ι → Finset β) :
    (∑ i ∈ I, (U i).card) -
      (∑ i ∈ I, (U i \ E.biUnion (fun e => L e i)).card) ≤
        ∑ e ∈ E, ∑ i ∈ I, (U i ∩ L e i).card := by
  have h := sum_card_le_sum_card_sdiff_biUnion_add_sum_card_inter I U E L
  omega

theorem sum_card_sub_sum_card_sdiff_biUnion_le
    (I : Finset ι) (U : ι → Finset β) (E : Finset ε)
    (L : ε → ι → Finset β) :
    (∑ i ∈ I, ((U i).card : ℝ)) -
      (∑ i ∈ I, ((U i \ E.biUnion (fun e => L e i)).card : ℝ)) ≤
        ∑ e ∈ E, ∑ i ∈ I, ((U i ∩ L e i).card : ℝ) := by
  have hnat := sum_card_le_sum_card_sdiff_biUnion_add_sum_card_inter I U E L
  have hreal := (Nat.cast_le (α := ℝ)).mpr hnat
  simp only [Nat.cast_add, Nat.cast_sum] at hreal
  linarith

end FiniteSets

section Configurations

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F] {n K : ℕ}

noncomputable def chunkFeasibleSet (data : Data F n) (U : Fin n → Finset (Point F))
    (E : Finset (Position n K)) (pool : Pool F n K) (i : Fin n) :
    Finset (Point F) := by
  classical
  exact (U i).filter (Feasible data E pool i)

@[simp] theorem mem_chunkFeasibleSet (data : Data F n)
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) (b : Point F) :
    b ∈ chunkFeasibleSet data U E pool i ↔ b ∈ U i ∧ Feasible data E pool i b := let _ := instFintypeF; by
  classical
  simp only [chunkFeasibleSet, Finset.mem_filter]

noncomputable def conflictingPoints (data : Data F n) (U : Finset (Point F))
    (i j : Fin n) (x : Point F) : Finset (Point F) := by
  classical
  exact U.filter fun b => Conflict data i j b x

@[simp] theorem mem_conflictingPoints (data : Data F n) (U : Finset (Point F))
    (i j : Fin n) (x b : Point F) :
    b ∈ conflictingPoints data U i j x ↔ b ∈ U ∧ Conflict data i j b x := let _ := instFintypeF; by
  classical
  simp only [conflictingPoints, Finset.mem_filter]

theorem chunkFeasibleSet_eq_sdiff_biUnion (data : Data F n)
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K))
    (pool : Pool F n K) (i : Fin n) :
    chunkFeasibleSet data U E pool i =
      U i \ E.biUnion (fun e => conflictingPoints data (U i) i e.1 (pool e)) := by
  classical
  ext b
  simp only [mem_chunkFeasibleSet, Finset.mem_sdiff, Finset.mem_biUnion,
    mem_conflictingPoints, Feasible]
  constructor
  · rintro ⟨hb, hfeasible⟩
    refine ⟨hb, ?_⟩
    rintro ⟨e, he, _, hconflict⟩
    exact hfeasible e he hconflict
  · rintro ⟨hb, havoid⟩
    refine ⟨hb, ?_⟩
    intro e he hconflict
    exact havoid ⟨e, he, hb, hconflict⟩

theorem chunkFeasibleSet_feasibleSet (data : Data F n)
    (P E : Finset (Position n K)) (pool : Pool F n K) (i : Fin n) :
    chunkFeasibleSet data (feasibleSet data P pool) E pool i =
      feasibleSet data (P ∪ E) pool i := by
  classical
  ext b
  simp only [mem_chunkFeasibleSet, mem_feasibleSet, Feasible, Finset.mem_union]
  constructor
  · rintro ⟨hP, hE⟩ e (he | he)
    · exact hP e he
    · exact hE e he
  · intro h
    exact ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩

theorem sum_card_sub_sum_card_chunkFeasibleSet_le_conflictingPoints
    (data : Data F n) (I : Finset (Fin n)) (U : Fin n → Finset (Point F))
    (E : Finset (Position n K)) (pool : Pool F n K) :
    (∑ i ∈ I, ((U i).card : ℝ)) -
      (∑ i ∈ I, ((chunkFeasibleSet data U E pool i).card : ℝ)) ≤
        ∑ e ∈ E, ∑ i ∈ I, ((conflictingPoints data (U i) i e.1 (pool e)).card : ℝ) := by
  classical
  have h := sum_card_sub_sum_card_sdiff_biUnion_le I U E
    (fun e i => conflictingPoints data (U i) i e.1 (pool e))
  simpa only [chunkFeasibleSet_eq_sdiff_biUnion, conflictingPoints,
    Finset.inter_filter, Finset.inter_self] using h

end Configurations

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

theorem card_conflictingPoints_le_equationLoss (data : Data F n)
    (U : Finset (Point F)) (i j : Fin n) (x : Point F) :
    ((conflictingPoints data U i j x).card : ℝ) ≤
      (∑ d ∈ data.dirs i, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
        equationLoss U d (projection d (v - u)) x) +
      (∑ d ∈ data.dirs j, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
        equationLoss U d (projection d (v - u)) x) := by
  classical
  let slices : Direction F → Point F → Point F → Finset (Point F) :=
    fun d u v => U.filter fun b =>
      projection d b = projection d x + projection d (v - u)
  let covered : Finset (Direction F) → Finset (Point F) := fun ds =>
    ds.biUnion fun d => (data.W i).biUnion fun u =>
      (data.W j).biUnion fun v => slices d u v
  have hcover : conflictingPoints data U i j x ⊆
      covered (data.dirs i) ∪ covered (data.dirs j) := by
    intro b hb
    obtain ⟨hbU, hconflict⟩ := (mem_conflictingPoints data U i j x b).mp hb
    obtain ⟨u, hu, v, hv, d, hd, heq⟩ :=
      (conflict_iff_forbidden data i j b x).mp hconflict
    have hmem (ds : Finset (Direction F)) (hd' : d ∈ ds) : b ∈ covered ds := by
      change b ∈ ds.biUnion (fun d => (data.W i).biUnion (fun u =>
        (data.W j).biUnion (fun v => slices d u v)))
      apply Finset.mem_biUnion.mpr
      refine ⟨d, hd', Finset.mem_biUnion.mpr ?_⟩
      refine ⟨u, hu, Finset.mem_biUnion.mpr ?_⟩
      refine ⟨v, hv, ?_⟩
      exact Finset.mem_filter.mpr ⟨hbU, heq⟩
    rcases Finset.mem_union.mp hd with hdi | hdj
    · exact Finset.mem_union.mpr (Or.inl (hmem _ hdi))
    · exact Finset.mem_union.mpr (Or.inr (hmem _ hdj))
  have hcount (ds : Finset (Direction F)) :
      (covered ds).card ≤
        ∑ d ∈ ds, ∑ u ∈ data.W i, ∑ v ∈ data.W j, (slices d u v).card := by
    dsimp only [covered]
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
    intro d hd
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
    intro u hu
    exact Finset.card_biUnion_le
  have hnat : (conflictingPoints data U i j x).card ≤
      (∑ d ∈ data.dirs i, ∑ u ∈ data.W i, ∑ v ∈ data.W j, (slices d u v).card) +
      (∑ d ∈ data.dirs j, ∑ u ∈ data.W i, ∑ v ∈ data.W j, (slices d u v).card) :=
    (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans
        (Nat.add_le_add (hcount (data.dirs i)) (hcount (data.dirs j))))
  have hreal := (Nat.cast_le (α := ℝ)).mpr hnat
  simpa only [Nat.cast_add, Nat.cast_sum, slices, equationLoss, sliceCount] using hreal

theorem sum_card_conflictingPoints_le_entryLoss (data : Data F n)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n) (x : Point F) :
    (∑ i ∈ I, ((conflictingPoints data (U i) i j x).card : ℝ)) ≤
      entryLoss data I U j x := by
  calc
    _ ≤ ∑ i ∈ I,
        ((∑ d ∈ data.dirs i, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
          equationLoss (U i) d (projection d (v - u)) x) +
        (∑ d ∈ data.dirs j, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
          equationLoss (U i) d (projection d (v - u)) x)) :=
      Finset.sum_le_sum fun i _ => card_conflictingPoints_le_equationLoss data (U i) i j x
    _ = entryLoss data I U j x := by
      rw [Finset.sum_add_distrib]
      rfl

theorem chunk_mass_loss_le_entryLoss (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (E : Finset (Position n K))
    (pool : Pool F n K) :
    frozenMass I U - frozenMass I (chunkFeasibleSet data U E pool) ≤
      ∑ e ∈ E, entryLoss data I U e.1 (pool e) := by
  refine (sum_card_sub_sum_card_chunkFeasibleSet_le_conflictingPoints
    data I U E pool).trans ?_
  exact Finset.sum_le_sum fun e _ =>
    sum_card_conflictingPoints_le_entryLoss data I U e.1 (pool e)

theorem feasibleMass_sub_le_entryLoss (data : Data F n) (I : Finset (Fin n))
    (P E : Finset (Position n K)) (pool : Pool F n K) :
    (feasibleMass data I P pool : ℝ) - (feasibleMass data I (P ∪ E) pool : ℝ) ≤
      ∑ e ∈ E, entryLoss data I (feasibleSet data P pool) e.1 (pool e) := by
  have h := chunk_mass_loss_le_entryLoss data I (feasibleSet data P pool) E pool
  simpa only [frozenMass, chunkFeasibleSet_feasibleSet, feasibleMass, Nat.cast_sum] using h

end RyserCoveringCounterexample.Selection

end OAI
