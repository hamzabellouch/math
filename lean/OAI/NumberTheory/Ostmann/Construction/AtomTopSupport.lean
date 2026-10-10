import OAI.NumberTheory.Ostmann.Construction.TopPrimeSupport
import OAI.NumberTheory.Ostmann.Construction.ExpandedScheduledTemplate

namespace OAI

/-! # The top atom support as explicit original-prime tests -/

namespace Ostmann

open scoped BigOperators Classical

/-- Every prime constituent of one atom is compared to every constituent of
each different atom. Repeated coordinates are deliberately retained. -/
noncomputable def atomPairChecks {I V : Type*} [Fintype I]
    (words : I → List V) : List (TopPrimeCondition V) :=
  Finset.univ.toList.flatMap fun i => Finset.univ.toList.flatMap fun j =>
    if i = j then [] else
      (words i).flatMap fun v => (words j).map (TopPrimeCondition.distinct v)

theorem atomPairChecks_iff {I V : Type*} [Fintype I]
    (words : I → List V) (x : V → ℕ) :
    (∀ c ∈ atomPairChecks words, c.Holds x) ↔
      Pairwise (fun i j => ((words i).map x).prod.Coprime ((words j).map x).prod) := by
  constructor
  · intro h i j hij
    rw [Nat.coprime_list_prod_left_iff]
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    rw [Nat.coprime_list_prod_right_iff]
    intro b hb
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hb
    apply h (.distinct v w)
    apply List.mem_flatMap.mpr
    refine ⟨i, by simp, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨j, by simp, ?_⟩
    rw [ite_eq_right hij]
    exact List.mem_flatMap.mpr ⟨v, hv, List.mem_map.mpr ⟨w, hw, rfl⟩⟩
  · intro h c hc
    obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨j, _, hc⟩ := List.mem_flatMap.mp hc
    by_cases hij : i = j
    · simp only [hij, ite_true, List.not_mem_nil] at hc
    · rw [ite_eq_right hij] at hc
      obtain ⟨v, hv, hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
      have hh : ((words i).map x).prod.Coprime ((words j).map x).prod := h hij
      rw [Nat.coprime_list_prod_left_iff] at hh
      have hh' := hh _ (List.mem_map.mpr ⟨v, hv, rfl⟩)
      rw [Nat.coprime_list_prod_right_iff] at hh'
      exact hh' _ (List.mem_map.mpr ⟨w, hw, rfl⟩)

theorem atomPairChecks_bounded {I V : Type*} [Fintype I]
    (words : I → List V) (R : ℝ) :
    ∀ c ∈ atomPairChecks words, c.Bounded R := by
  intro c hc
  obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨j, _, hc⟩ := List.mem_flatMap.mp hc
  by_cases hij : i = j
  · simp only [hij, ite_true, List.not_mem_nil] at hc
  · simp only [hij, ite_false] at hc
    obtain ⟨v, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hc
    trivial

theorem atomPairChecks_length {I V : Type*} [Fintype I]
    (words : I → List V) (M : ℕ) (hw : ∀ i, (words i).length ≤ M) :
    (atomPairChecks words).length ≤ (Fintype.card I * M) ^ 2 := by
  have hp (i j : I) :
      (if i = j then [] else (words i).flatMap fun v =>
        (words j).map (TopPrimeCondition.distinct v)).length ≤ M * M := by
    split_ifs
    · simp only [List.length_nil]; omega
    · apply (list_flatMap_length_bound (words i) _ M
        (fun _ _ => by simpa only [List.length_map] using hw j)).trans
      exact Nat.mul_le_mul_right M (hw i)
  have hi (i : I) :
      (Finset.univ.toList.flatMap fun j => if i = j then [] else
        (words i).flatMap fun v => (words j).map (TopPrimeCondition.distinct v)).length ≤
          Fintype.card I * (M * M) := by
    simpa only [Finset.length_toList, Finset.card_univ] using
      list_flatMap_length_bound Finset.univ.toList _ (M * M) (fun j _ => hp i j)
  calc
    _ ≤ Fintype.card I * (Fintype.card I * (M * M)) := by
      simpa only [atomPairChecks, Finset.length_toList, Finset.card_univ] using
        list_flatMap_length_bound Finset.univ.toList _ (Fintype.card I * (M * M)) (fun i _ => hi i)
    _ = _ := by ring

noncomputable def atomExternalChecks {I V : Type*} [Fintype I]
    (words : I → List V) (N : ℤ) : List (TopPrimeCondition V) :=
  Finset.univ.toList.flatMap fun i => (words i).map (fun v => .external v N)

theorem atomExternalChecks_iff {I V : Type*} [Fintype I]
    (words : I → List V) (N : ℤ) (x : V → ℕ) :
    (∀ c ∈ atomExternalChecks words N, c.Holds x) ↔
      ∀ i, ((words i).map x).prod.Coprime N.natAbs := by
  constructor
  · intro h i
    rw [Nat.coprime_list_prod_left_iff]
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact h (.external v N) (List.mem_flatMap.mpr
      ⟨i, by simp, List.mem_map.mpr ⟨v, hv, rfl⟩⟩)
  · intro h c hc
    obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    exact Nat.coprime_list_prod_left_iff.mp (h i) _ (List.mem_map.mpr ⟨v, hv, rfl⟩)

theorem atomExternalChecks_bounded {I V : Type*} [Fintype I]
    (words : I → List V) (N : ℤ) (R : ℝ) (hN : |(N : ℝ)| ≤ R) :
    ∀ c ∈ atomExternalChecks words N, c.Bounded R := by
  intro c hc
  obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hc
  exact hN

theorem atomExternalChecks_length {I V : Type*} [Fintype I]
    (words : I → List V) (N : ℤ) (M : ℕ) (hw : ∀ i, (words i).length ≤ M) :
    (atomExternalChecks words N).length ≤ Fintype.card I * M := by
  simpa only [atomExternalChecks, Finset.length_toList, Finset.card_univ] using
    list_flatMap_length_bound Finset.univ.toList _ M
      (fun i _ => by simpa only [List.length_map] using hw i)

end Ostmann

end OAI
