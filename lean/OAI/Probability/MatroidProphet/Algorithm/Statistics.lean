import OAI.Probability.MatroidProphet.Algorithm.LayerRank
import OAI.Probability.MatroidProphet.PathStatistics

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Set Finset Pivots
variable {n : ℕ}

noncomputable def pathGroups (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (h : ℕ) : Finset (Fin n) := by
  classical
  exact (groupMask M d w univ h).toFinset

lemma pathGroups_coe (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (h : ℕ) :
    (pathGroups M d w h : Set (Fin n)) = groupMask M d w univ h := by
  classical
  exact Set.coe_toFinset _

lemma groupMask_eq_inter (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (mask : Finset (Fin n)) (h : ℕ) :
    groupMask M d w mask h = (mask : Set (Fin n)) ∩ (pathGroups M d w h : Set (Fin n)) := by
  classical
  rw [pathGroups_coe]
  ext e
  simp [groupMask]

lemma pathGroups_disjoint (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) : Pairwise (fun i j => Disjoint (pathGroups M d w i) (pathGroups M d w j)) := by
  classical
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  have heI : e ∈ groupMask M d w univ i := by simpa only [pathGroups, Set.mem_toFinset] using hei
  have heJ : e ∈ groupMask M d w univ j := by simpa only [pathGroups, Set.mem_toFinset] using hej
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp heI.2.1.1
  have hi := (groups_index_of_get M d w (heI.2.2.symm.trans hk)).2
  have hj := (groups_index_of_get M d w (heJ.2.2.symm.trans hk)).2
  exact hij (hi.symm.trans hj)

noncomputable def listedLambda (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) : ℕ :=
  finalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w d.T) h (groups M d w).length (groupMask M d w univ h)
    ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (d.T : Set (Fin n)) (boolParity d.odd)

noncomputable def listedZ (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) : ℕ :=
  nominalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w d.T) h (groupMask M d w univ h)
    ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (boolParity d.odd)

noncomputable def trueLambda (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ) : ℕ := by
  classical
  exact if i ∈ groups M d w then listedLambda M hE d w ((groups M d w).idxOf i) else 0

noncomputable def trueZ (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (i : ℤ) : ℕ := by
  classical
  exact if i ∈ groups M d w then listedZ M hE d w ((groups M d w).idxOf i) else 0

theorem listedLambda_le_count (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n) (h : ℕ) :
    listedLambda M hE d w h ≤
      ((selection M hE d w π).filter (fun e =>
        ∃ i, w e = some i ∧ h ≤ (groups M d w).idxOf i)).card := by
  classical
  have hc := selection_cumulative_rank M hE d w π h
    (parityPoints (activation h) (boolParity d.odd)) (by
      intro b hb
      have hm := ((mem_parityPoints _ _ _).mp hb).2.2
      rwa [boolParity_val] at hm)
  rw [sum_parityPoints] at hc
  have hreg (b : ParityWindow (activation h) (boolParity d.odd)) :
      groupBirthRegion M hE d w h b.val.val =
        nominalLayerSet M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
          h (groupMask M d w univ h) (boolParity d.odd) b \
          ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) :=
    unobservedBirthRegion_eq_nominalLayer M hE (2^100) _ _ h _ _ _ b
  simp_rw [hreg] at hc
  exact hc

theorem trueLambda_le_count (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (π : ArrivalOrder n) (i : ℤ) :
    trueLambda M hE d w i ≤
      ((selection M hE d w π).filter (fun e => ∃ j, w e = some j ∧ i ≤ j)).card := by
  classical
  unfold trueLambda
  split_ifs with hi
  · apply (listedLambda_le_count M hE d w π _).trans
    apply Finset.card_le_card
    intro e he
    obtain ⟨hea, j, hwj, hij⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨hea, j, hwj, ?_⟩
    have hel := layerGreedy_subset M _ _ _ _ hea
    obtain ⟨k, hwk, hek, _⟩ := (assign_spec M hE d w e _ _).mp
      (assigned_some_of_eligible (assign M hE d w) w e hel)
    have hjk : j = k := Option.some.inj (hwj.symm.trans hwk)
    have hj : j ∈ groups M d w := hjk ▸ hek.2.2.1
    by_contra hn
    have hlt := (groups_idxOf_lt_iff M d w j i hj hi).mpr (by omega)
    omega
  · exact Nat.zero_le _

end MatroidProphet.MainAlgorithm

end OAI
