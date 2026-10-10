import OAI.Geometry.PeriodicTiling.ResidueLiftPairs
import OAI.Geometry.PeriodicTiling.ResidueCountBound
import OAI.Geometry.PeriodicTiling.DisjointSuccessorPairs
import OAI.Geometry.PeriodicTiling.FinitePairRatio
import OAI.Geometry.PeriodicTiling.FiniteEventUnion
import OAI.Geometry.PeriodicTiling.MarkedTile
import Mathlib.Tactic.Push

namespace OAI

universe uV uC uI

namespace PeriodicTilingThree

open scoped Classical

private def residueSuccessor (m : ℕ) (d : Lattice 3) : Equiv.Perm (Residue3 m) where
  toFun u := u + residueMod m d
  invFun u := u - residueMod m d
  left_inv u := add_sub_cancel_right u _
  right_inv u := sub_add_cancel u _

private theorem exists_residue_pairs
    {D : Finset (Lattice 3)} (hD : ∀ d, d ∈ D ↔ Requested 64 d) (d : ↥D) :
    ∃ pair : (Fin 32000 × Fin 2) ↪ Residue3 64,
      (∀ j, pair (j, 1) = pair (j, 0) + residueMod 64 d.1) ∧
      ∀ x, pair x ≠ 0 := by
  have hd : Requested 64 d.1 := (hD d.1).mp d.2
  exact exists_disjoint_successor_pairs (residueSuccessor 64 d.1)
    (requested_successor_ne hd) 0 32000 (by rw [card_residue3]; norm_num)

private noncomputable def residuePairs
    {D : Finset (Lattice 3)} (hD : ∀ d, d ∈ D ↔ Requested 64 d) (d : ↥D) :
    (Fin 32000 × Fin 2) ↪ Residue3 64 :=
  Classical.choose (exists_residue_pairs hD d)

private theorem residuePairs_step
    {D : Finset (Lattice 3)} (hD : ∀ d, d ∈ D ↔ Requested 64 d)
    (d : ↥D) (j : Fin 32000) :
    residuePairs hD d (j, 1) = residuePairs hD d (j, 0) + residueMod 64 d.1 :=
  (Classical.choose_spec (exists_residue_pairs hD d)).1 j

private theorem residuePairs_ne_zero
    {D : Finset (Lattice 3)} (hD : ∀ d, d ∈ D ↔ Requested 64 d)
    (d : ↥D) (x : Fin 32000 × Fin 2) : residuePairs hD d x ≠ 0 :=
  (Classical.choose_spec (exists_residue_pairs hD d)).2 x

private noncomputable def residuePairGood
    {D : Finset (Lattice 3)} (hD : ∀ d, d ∈ D ↔ Requested 64 d)
    (d : ↥D) (j : Fin 32000) : Finset (LiftAlphabet × LiftAlphabet) :=
  PairGood 64 d.1 (residuePairs hD d (j, 0)) (residuePairs hD d (j, 1))

private theorem normalized_bad_assignment_ratio
    {V : Type uV} {C : Type uC} [Fintype V] [Fintype C] {k : ℕ}
    (pair : (Fin k × Fin 2) ↪ V) (Good : Fin k → Finset (C × C))
    (Bad : Finset (V → C)) (hBad : Bad = allBadAssignments pair Good)
    (N : ℕ) (hN : N = Fintype.card C ^ Fintype.card V)
    (hC : Fintype.card C = 125) (hgood : ∀ j, 27 ≤ (Good j).card) :
    (Bad.card : ℚ) / (N : ℚ) ≤ ((15598 : ℚ) / 15625) ^ k := by
  have hCpos : 0 < Fintype.card C := by rw [hC]; norm_num
  have hg : 27 ≤ Fintype.card C ^ 2 := by rw [hC]; norm_num
  have heq : (1 : ℚ) - ((27 : ℕ) : ℚ) / (Fintype.card C : ℚ) ^ 2 =
      15598 / 15625 := by
    rw [hC]
    norm_num
  have h := allBadAssignments_card_ratio_le pair Good 27 hCpos hg hgood
  rw [Fintype.card_fun, ← hN, ← hBad, heq] at h
  exact h

private theorem residuePairGood_card
    {D : Finset (Lattice 3)} (hD : ∀ d, d ∈ D ↔ Requested 64 d)
    (d : ↥D) (j : Fin 32000) : 27 ≤ (residuePairGood hD d j).card := by
  have hd : Requested 64 d.1 := (hD d.1).mp d.2
  exact card_PairGood_ge (m := 64) (d := d.1)
    (u := residuePairs hD d (j, 0)) (v := residuePairs hD d (j, 1))
    hd (residuePairs_step hD d j)

private theorem representative_difference_of_pairGood {m : ℕ} [NeZero m]
    (ω : LiftAssignment m) (d : Lattice 3) (u v : Residue3 m) :
    (ω u, ω v) ∈ PairGood m d u v →
      representative m ω v - representative m ω u = d := by
  have hiff := pairGood_assignment_iff (m := m) (d := d) ω u v
  generalize hset : PairGood m d u v = S at hiff ⊢
  exact hiff.mp

private theorem exists_good_pair {V : Type uV} {C : Type uC} [Fintype V] [Fintype C] {k : ℕ}
    (pair : (Fin k × Fin 2) ↪ V) (Good : Fin k → Finset (C × C)) (ω : V → C)
    (P : Fin k → Prop)
    (hP : ∀ j, (ω (pair (j, 0)), ω (pair (j, 1))) ∈ Good j → P j)
    (hbad : ω ∉ allBadAssignments pair Good) : ∃ j, P j := by
  rw [mem_allBadAssignments] at hbad
  push Not at hbad
  obtain ⟨j, hj⟩ := hbad
  exact ⟨j, hP j hj⟩

private theorem exists_simultaneous_good_pairs
    {I : Type uI} {V : Type uV} {C : Type uC} [Fintype V] [Fintype C] {k : ℕ}
    (events : Finset I) (pair : I → (Fin k × Fin 2) ↪ V)
    (Good : I → Fin k → Finset (C × C))
    (hC : Fintype.card C = 125) (hgood : ∀ i j, 27 ≤ (Good i j).card)
    (P : I → (V → C) → Fin k → Prop)
    (hP : ∀ i ω j, (ω (pair i (j, 0)), ω (pair i (j, 1))) ∈ Good i j → P i ω j)
    (hsmall : (events.card : ℚ) * ((15598 : ℚ) / 15625) ^ k < 1) :
    ∃ ω : V → C, ∀ i ∈ events, ∃ j, P i ω j := by
  classical
  have hΩ : 0 < Fintype.card (V → C) := by
    rw [Fintype.card_fun, hC]
    exact pow_pos (by norm_num) _
  have hbound (i : I) :
      ((allBadAssignments (pair i) (Good i)).card : ℚ) /
          (Fintype.card (V → C) : ℚ) ≤ ((15598 : ℚ) / 15625) ^ k := by
    exact normalized_bad_assignment_ratio (pair i) (Good i)
      (allBadAssignments (pair i) (Good i)) rfl (Fintype.card (V → C))
      (by rw [Fintype.card_fun]) hC (hgood i)
  obtain ⟨ω, hω⟩ := exists_avoiding_of_uniform_ratio_lt events
    (fun i => allBadAssignments (pair i) (Good i))
    (((15598 : ℚ) / 15625) ^ k) hΩ (fun i _ => hbound i) hsmall
  refine ⟨ω, ?_⟩
  intro i hi
  exact exists_good_pair (pair i) (Good i) ω (P i ω) (hP i ω) (hω i hi)

private theorem exists_rigid_assignment_of_requests
    (D : Finset (Lattice 3)) (hD : ∀ d, d ∈ D ↔ Requested 64 d)
    (hcardD : D.card ≤ 129 ^ 3) :
    ∃ ω : LiftAssignment 64, ∀ d : Lattice 3, Requested 64 d →
      ∃ u v : Residue3 64, u ≠ 0 ∧ v ≠ 0 ∧
        representative 64 ω v - representative 64 ω u = d := by
  classical
  have hcard : (Finset.univ : Finset ↥D).card ≤ 129 ^ 3 := by
    rw [Finset.card_univ, Fintype.card_coe]
    exact hcardD
  have hsmall : ((Finset.univ : Finset ↥D).card : ℚ) *
      ((15598 : ℚ) / 15625) ^ 32000 < 1 := by
    apply lt_of_le_of_lt _ residue_union_bound_32000
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast hcard
    · exact pow_nonneg (by norm_num) _
  have himp (e : ↥D) (ω : LiftAssignment 64) (j : Fin 32000) :
      (ω (residuePairs hD e (j, 0)), ω (residuePairs hD e (j, 1))) ∈
        residuePairGood hD e j →
      representative 64 ω (residuePairs hD e (j, 1)) -
        representative 64 ω (residuePairs hD e (j, 0)) = e.1 := by
    dsimp only [residuePairGood]
    exact representative_difference_of_pairGood (m := 64) ω e.1
      (residuePairs hD e (j, 0)) (residuePairs hD e (j, 1))
  obtain ⟨ω, hω⟩ := exists_simultaneous_good_pairs
    (Finset.univ : Finset ↥D) (residuePairs hD) (residuePairGood hD)
    card_liftAlphabet (residuePairGood_card hD)
    (fun e ω j => representative 64 ω (residuePairs hD e (j, 1)) -
      representative 64 ω (residuePairs hD e (j, 0)) = e.1) himp hsmall
  refine ⟨ω, ?_⟩
  intro d hd
  let e : ↥D := ⟨d, (hD d).mpr hd⟩
  obtain ⟨j, hj⟩ := hω e (Finset.mem_univ _)
  exact ⟨residuePairs hD e (j, 0), residuePairs hD e (j, 1),
    residuePairs_ne_zero hD e (j, 0), residuePairs_ne_zero hD e (j, 1), hj⟩

theorem exists_rigid_assignment64 :
    ∃ ω : LiftAssignment 64, ∀ d : Lattice 3, Requested 64 d →
      ∃ u v : Residue3 64, u ≠ 0 ∧ v ≠ 0 ∧
        representative 64 ω v - representative 64 ω u = d := by
  exact exists_rigid_assignment_of_requests (requestedVectors 64)
    (fun d => mem_requestedVectors (m := 64) (d := d)) (card_requestedVectors_le 64)

noncomputable def rigidAssignment64 : LiftAssignment 64 :=
  Classical.choose exists_rigid_assignment64

theorem rigidAssignment64_difference (d : Lattice 3) (hd : Requested 64 d) :
    ∃ u v : Residue3 64, u ≠ 0 ∧ v ≠ 0 ∧
      representative 64 rigidAssignment64 v - representative 64 rigidAssignment64 u = d :=
  Classical.choose_spec exists_rigid_assignment64 d hd

noncomputable def rigidSection : MarkedTile.ResidueSection 64 where
  t := representative 64 rigidAssignment64
  residue_t v := representative_residue 64 rigidAssignment64 v

theorem rigidSection_difference (d : Lattice 3) (hd : Requested 64 d) :
    ∃ u v : MarkedTile.Residue 64, u ≠ 0 ∧ v ≠ 0 ∧ rigidSection.t v - rigidSection.t u = d :=
  rigidAssignment64_difference d hd

private theorem section_difference_to_Tstar {m : ℕ} [NeZero m]
    (s : MarkedTile.ResidueSection m) (d : Lattice 3)
    (h : ∃ u v : MarkedTile.Residue m,
      u ≠ 0 ∧ v ≠ 0 ∧ s.t v - s.t u = d) :
    ∃ x ∈ s.Tstar, ∃ y ∈ s.Tstar, x - y = d := by
  obtain ⟨u, v, hu, hv, hdiff⟩ := h
  have hvT : s.t v ∈ s.Tstar :=
    (s.mem_Tstar (x := s.t v)).mpr ⟨v, hv, rfl⟩
  have huT : s.t u ∈ s.Tstar :=
    (s.mem_Tstar (x := s.t u)).mpr ⟨u, hu, rfl⟩
  exact ⟨s.t v, hvT, s.t u, huT, hdiff⟩

theorem rigidSection_Tstar_difference (d : Lattice 3) (hd : Requested 64 d) :
    ∃ x ∈ rigidSection.Tstar, ∃ y ∈ rigidSection.Tstar, x - y = d := by
  exact section_difference_to_Tstar rigidSection d (rigidSection_difference d hd)

end PeriodicTilingThree

end OAI
