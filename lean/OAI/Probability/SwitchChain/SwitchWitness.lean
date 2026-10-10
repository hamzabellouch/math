import Mathlib

namespace OAI

open scoped BigOperators

namespace Problem315

namespace Havel

section FinsetWitness

variable {V : Type*} [DecidableEq V]

theorem exists_top_subset (R : Finset V) (w : V → Nat) (q : Nat)
    (hq : q ≤ R.card) :
    ∃ T ⊆ R, T.card = q ∧ ∀ i ∈ R, i ∉ T → ∀ j ∈ T, w i ≤ w j := by
  classical
  obtain ⟨T₀, hT₀R, hT₀q⟩ := Finset.exists_subset_card_eq hq
  have hnonempty : (R.powersetCard q).Nonempty :=
    ⟨T₀, Finset.mem_powersetCard.mpr ⟨hT₀R, hT₀q⟩⟩
  obtain ⟨T, hT, hmax⟩ :=
    Finset.exists_max_image (R.powersetCard q) (fun S => ∑ i ∈ S, w i) hnonempty
  obtain ⟨hTR, hTq⟩ := Finset.mem_powersetCard.mp hT
  refine ⟨T, hTR, hTq, ?_⟩
  intro i hiR hiT j hjT
  have hiErase : i ∉ T.erase j := fun h => hiT (Finset.mem_of_mem_erase h)
  have hswap : insert i (T.erase j) ∈ R.powersetCard q := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hiR
      · exact hTR (Finset.mem_of_mem_erase hx)
    · rw [Finset.card_insert_of_notMem hiErase, Finset.card_erase_of_mem hjT]
      have hpos := Finset.card_pos.mpr ⟨j, hjT⟩
      omega
  have hbound := hmax _ hswap
  rw [Finset.sum_insert hiErase] at hbound
  have hsum := Finset.sum_erase_add T w hjT
  omega

theorem exists_prescribed_neighborhood (R : Finset V) (d : V → Nat) (v : V)
    (hq : d v ≤ (R.erase v).card) :
    ∃ T ⊆ R, v ∉ T ∧ T.card = d v ∧
      ∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T, d i ≤ d j := by
  classical
  obtain ⟨T, hTR, hTq, hsort⟩ := exists_top_subset (R.erase v) d (d v) hq
  refine ⟨T, fun x hx => Finset.mem_of_mem_erase (hTR hx), ?_, hTq, ?_⟩
  · intro hv
    exact Finset.notMem_erase v R (hTR hv)
  · intro i hiR hiv hiT j hjT
    exact hsort i (Finset.mem_erase.mpr ⟨hiv, hiR⟩) hiT j hjT

theorem exists_switch_witness_in (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset V)
    {v i j : V} (hvR : v ∈ R) (hiR : i ∈ R) (hjR : j ∈ R)
    (hvi : G.Adj v i) (hvj : ¬ G.Adj v j) (hvj_ne : v ≠ j)
    (hdeg : (R.filter (G.Adj i)).card ≤ (R.filter (G.Adj j)).card) :
    ∃ k ∈ R, k ≠ v ∧ k ≠ i ∧ k ≠ j ∧ G.Adj j k ∧ ¬ G.Adj i k := by
  classical
  let A := (R.filter (G.Adj i)).erase j
  let B := (R.filter (G.Adj j)).erase i
  have hcard : A.card ≤ B.card := by
    dsimp [A, B]
    simp only [Finset.card_erase_eq_ite, Finset.mem_filter, hiR, hjR, true_and]
    by_cases hij : G.Adj i j
    · have hji := hij.symm
      simp only [hij, hji, ite_true]
      omega
    · have hji : ¬ G.Adj j i := fun h => hij h.symm
      simpa only [hij, hji, ite_false] using hdeg
  have hvA : v ∈ A := by
    exact Finset.mem_erase.mpr ⟨hvj_ne, Finset.mem_filter.mpr ⟨hvR, hvi.symm⟩⟩
  have hvB : v ∉ B := by
    intro h
    exact hvj (Finset.mem_filter.mp (Finset.mem_of_mem_erase h)).2.symm
  have hcard' : (A.erase v).card < B.card :=
    lt_of_lt_of_le (Finset.card_erase_lt_of_mem hvA) hcard
  obtain ⟨k, hkB, hkA⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard'
  have hkv : k ≠ v := by
    intro h
    exact hvB (h ▸ hkB)
  have hkA' : k ∉ A := by
    intro h
    exact hkA (Finset.mem_erase.mpr ⟨hkv, h⟩)
  have hki : k ≠ i := (Finset.mem_erase.mp hkB).1
  have hkR : k ∈ R := (Finset.mem_filter.mp (Finset.mem_erase.mp hkB).2).1
  have hjk : G.Adj j k := (Finset.mem_filter.mp (Finset.mem_erase.mp hkB).2).2
  have hkj : k ≠ j := hjk.ne.symm
  refine ⟨k, hkR, hkv, hki, hkj, hjk, ?_⟩
  intro hik
  exact hkA' (Finset.mem_erase.mpr ⟨hkj, Finset.mem_filter.mpr ⟨hkR, hik⟩⟩)

theorem exists_improving_switch (G : SimpleGraph V) [DecidableRel G.Adj]
    (R T : Finset V) {v : V} (hvR : v ∈ R) (hTR : T ⊆ R) (hvT : v ∉ T)
    (hsize : T.card = (R.filter (G.Adj v)).card)
    (hsorted : ∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T,
      (R.filter (G.Adj i)).card ≤ (R.filter (G.Adj j)).card)
    (hne : R.filter (G.Adj v) ≠ T) :
    ∃ i ∈ R, ∃ j ∈ T, ∃ k ∈ R,
      i ∉ T ∧ ¬ G.Adj v j ∧ G.Adj v i ∧ G.Adj j k ∧ ¬ G.Adj i k ∧
      v ≠ j ∧ k ≠ v ∧ k ≠ i ∧ k ≠ j := by
  classical
  have hnot_sub : ¬ R.filter (G.Adj v) ⊆ T := by
    intro h
    exact hne (Finset.eq_of_subset_of_card_le h hsize.le)
  obtain ⟨i, hiN, hiT⟩ := Finset.not_subset.mp hnot_sub
  have hnot_sub' : ¬ T ⊆ R.filter (G.Adj v) := by
    intro h
    exact hne (Finset.eq_of_subset_of_card_le h hsize.ge).symm
  obtain ⟨j, hjT, hjN⟩ := Finset.not_subset.mp hnot_sub'
  obtain ⟨hiR, hvi⟩ := Finset.mem_filter.mp hiN
  have hjR := hTR hjT
  have hvj : ¬ G.Adj v j := by
    intro h
    exact hjN (Finset.mem_filter.mpr ⟨hjR, h⟩)
  have hvj_ne : v ≠ j := by
    intro h
    exact hvT (h ▸ hjT)
  have hdeg := hsorted i hiR hvi.ne.symm hiT j hjT
  obtain ⟨k, hkR, hkv, hki, hkj, hjk, hik⟩ :=
    exists_switch_witness_in G R hvR hiR hjR hvi hvj hvj_ne hdeg
  exact ⟨i, hiR, j, hjT, k, hkR, hiT, hvj, hvi, hjk, hik,
    hvj_ne, hkv, hki, hkj⟩

end FinsetWitness

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_switch_witness (G : SimpleGraph V) [DecidableRel G.Adj]
    {v i j : V} (hvi : G.Adj v i) (hvj : ¬ G.Adj v j)
    (hvj_ne : v ≠ j) (hdeg : G.degree i ≤ G.degree j) :
    ∃ k : V, k ≠ v ∧ k ≠ i ∧ k ≠ j ∧ G.Adj j k ∧ ¬ G.Adj i k := by
  classical
  let A := (G.neighborFinset i).erase j
  let B := (G.neighborFinset j).erase i
  have hcard : A.card ≤ B.card := by
    dsimp [A, B]
    simp only [Finset.card_erase_eq_ite, G.mem_neighborFinset,
      G.card_neighborFinset_eq_degree]
    by_cases hij : G.Adj i j
    · have hji := hij.symm
      simp only [hij, hji, ite_true]
      omega
    · have hji : ¬ G.Adj j i := fun h => hij h.symm
      simpa only [hij, hji, ite_false] using hdeg
  have hvA : v ∈ A := by
    simp only [A, Finset.mem_erase, G.mem_neighborFinset]
    exact ⟨hvj_ne, hvi.symm⟩
  have hvB : v ∉ B := by
    intro h
    exact hvj ((G.mem_neighborFinset j v).mp (Finset.mem_of_mem_erase h)).symm
  have hcard' : (A.erase v).card < B.card :=
    lt_of_lt_of_le (Finset.card_erase_lt_of_mem hvA) hcard
  obtain ⟨k, hkB, hkA⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard'
  have hkv : k ≠ v := by
    intro h
    exact hvB (h ▸ hkB)
  have hkA' : k ∉ A := by
    intro h
    exact hkA (Finset.mem_erase.mpr ⟨hkv, h⟩)
  have hki : k ≠ i := (Finset.mem_erase.mp hkB).1
  have hjk : G.Adj j k :=
    (G.mem_neighborFinset j k).mp (Finset.mem_erase.mp hkB).2
  have hkj : k ≠ j := hjk.ne.symm
  refine ⟨k, hkv, hki, hkj, hjk, ?_⟩
  intro hik
  exact hkA' (Finset.mem_erase.mpr ⟨hkj, (G.mem_neighborFinset i k).mpr hik⟩)

end Havel

end Problem315

end OAI
