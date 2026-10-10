import OAI.InformationTheory.QuantumCircuit.PauliBasis

namespace OAI

/-! Pauli coefficient and support bounds for low-degree operators. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace QAC

def pauliFiber (N : ℕ) (S : Finset (Fin N)) : Finset (Fin N → Fin 4) :=
  Finset.univ.filter (fun w => pauliSupport w = S)

lemma pauliFiber_card (N : ℕ) (S : Finset (Fin N)) :
    (pauliFiber N S).card ≤ 3^S.card := by
  classical
  let f : ↥(pauliFiber N S) → (S → {a : Fin 4 // a ≠ 0}) := fun w i =>
    ⟨w.val i, by
      have hs : pauliSupport w.val = S := (Finset.mem_filter.mp w.property).2
      have hi : i.val ∈ pauliSupport w.val := hs.symm ▸ i.property
      exact (Finset.mem_filter.mp hi).2⟩
  have hf : Function.Injective f := by
    intro w v heq
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · exact congrArg Subtype.val (congrFun heq ⟨i, hi⟩)
    · have hw : w.val i = 0 := by
        by_contra hw
        have hs : pauliSupport w.val = S := (Finset.mem_filter.mp w.property).2
        exact hi (hs ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ i, hw⟩)
      have hv : v.val i = 0 := by
        by_contra hv
        have hs : pauliSupport v.val = S := (Finset.mem_filter.mp v.property).2
        exact hi (hs ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ i, hv⟩)
      exact hw.trans hv.symm
  have hc := Fintype.card_le_of_injective f hf
  have hn : Fintype.card {a : Fin 4 // a ≠ 0} = 3 := by decide
  simpa only [Fintype.card_coe, Fintype.card_fun, hn] using hc

def lowPaulis (N ell : ℕ) : Finset (Fin N → Fin 4) :=
  Finset.univ.filter (fun w => (pauliSupport w).card ≤ ell)

lemma lowPaulis_card {N ell : ℕ} (hN : 1 ≤ N) :
    (lowPaulis N ell).card ≤ (ell + 1) * (3 * N)^ell := by
  classical
  let layers := fun j => (Finset.univ : Finset (Fin N)).powersetCard j
  have hsub : lowPaulis N ell ⊆ (Finset.range (ell + 1)).biUnion
      (fun j => (layers j).biUnion (pauliFiber N)) := by
    intro w hw
    have hw' := (Finset.mem_filter.mp hw).2
    refine Finset.mem_biUnion.mpr ⟨(pauliSupport w).card, by simp; omega, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨pauliSupport w,
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩, ?_⟩
    simp [pauliFiber]
  calc
    _ ≤ ((Finset.range (ell + 1)).biUnion (fun j => (layers j).biUnion (pauliFiber N))).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (ell + 1), ((layers j).biUnion (pauliFiber N)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.range (ell + 1), ∑ S ∈ layers j, (pauliFiber N S).card :=
      Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le)
    _ ≤ ∑ j ∈ Finset.range (ell + 1), (3 * N)^j := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ∑ S ∈ layers j, 3^j := by
          apply Finset.sum_le_sum
          intro S hS
          have hc : S.card = j := (Finset.mem_powersetCard.mp hS).2
          simpa only [hc] using pauliFiber_card N S
        _ = N.choose j * 3^j := by simp [layers, Finset.card_powersetCard]
        _ ≤ N^j * 3^j := Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)
        _ = _ := by rw [← mul_pow, Nat.mul_comm]
    _ ≤ ∑ _j ∈ Finset.range (ell + 1), (3 * N)^ell := by
      apply Finset.sum_le_sum
      intro j hj
      exact Nat.pow_le_pow_right (by omega) (by have := Finset.mem_range.mp hj; omega)
    _ = _ := by simp

lemma pauli_expansion_low {N ell : ℕ} (E : Operator N) (hE : HasDegreeLE E ell) :
    (∑ w ∈ lowPaulis N ell, pauliCoefficient E w • pauliTensor w) = E := by
  classical
  calc
    _ = ∑ w : Fin N → Fin 4, pauliCoefficient E w • pauliTensor w := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro w _ hw
      have hh : ell < (pauliSupport w).card := by
        have hn : ¬ (pauliSupport w).card ≤ ell := by simpa [lowPaulis] using hw
        omega
      rw [pauliCoefficient_degree_zero E hE w hh, zero_smul]
    _ = E := pauli_expansion E

def pauliExpansionTerm {N : ℕ} (E : Operator N) (w : Fin N → Fin 4) : LocalExpansionTerm N where
  coeff := pauliCoefficient E w
  gates := fun i => ⟨pauli (w i), pauli_unitary (w i)⟩
  support := pauliSupport w
  outside := by
    intro i hi
    have hw : w i = 0 := by simpa [pauliSupport] using hi
    apply Subtype.ext
    simp [hw]

theorem published_pauli_expansion : PublishedPauliExpansion := by
  classical
  intro N ell hN E hE
  let terms := (lowPaulis N ell).toList.map (pauliExpansionTerm E)
  refine ⟨terms, ?_, ?_, ?_⟩
  · dsimp [terms]
    rw [List.map_map]
    change E = ((lowPaulis N ell).toList.map
      (fun w => pauliCoefficient E w • pauliTensor w)).sum
    rw [← List.sum_toFinset _ (lowPaulis N ell).nodup_toList, Finset.toList_toFinset]
    exact (pauli_expansion_low E hE).symm
  · intro t ht
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hw)).2
  · dsimp [terms]
    rw [List.map_map]
    change ((lowPaulis N ell).toList.map (fun w => ‖pauliCoefficient E w‖)).sum ≤ _
    rw [← List.sum_toFinset _ (lowPaulis N ell).nodup_toList, Finset.toList_toFinset]
    calc
      _ ≤ ∑ _w ∈ lowPaulis N ell, ‖E‖ := Finset.sum_le_sum (fun w _ => pauliCoefficient_norm E w)
      _ = ((lowPaulis N ell).card : ℝ) * ‖E‖ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast lowPaulis_card (ell := ell) hN) (norm_nonneg E)

end QAC

end

end OAI
