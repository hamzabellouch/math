import OAI.Probability.ContinuumTransition.FixedOccupation

namespace OAI

universe u_1

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem fixedOccupation_binary_eq {κ : Type u_1} (A : κ → Set Space) (n : κ → ℕ)
    {s : Finset κ} {i : κ} (hi : i ∉ s)
    (hd : (↑(insert i s) : Set κ).Pairwise (fun j k => Disjoint (A j) (A k)))
    {U : Space → Space → ℝ} (hU : ∀ x y, U x y = U y x) (β h : ℝ)
    (hcross : ∀ j ∈ insert i s, ∀ k ∈ insert i s, j ≠ k →
      ∀ a ∈ A j, ∀ b ∈ A k, U a b = 0)
    {ι : Type} [Fintype ι] [DecidableEq ι] (r : Finset ι) {x : ι → Space}
    (hx : x ∈ binaryRegion (A i) (⋃ k ∈ s, A k) r) :
    fixedOccupationFamily A (insert i s) n (gibbsFamily U β h) ι x =
      countFamily (gibbsFamily U β h) (n i) {j : ι // j ∈ r} (fun j => x j)*
      fixedOccupationFamily A s n (gibbsFamily U β h) {j : ι // j ∉ r} (fun j => x j) := by
  have hid (k : κ) (hk : k ∈ s) : Disjoint (A i) (A k) :=
    hd (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hk) (fun hh => hi (hh ▸ hk))
  have hdU : Disjoint (A i) (⋃ k ∈ s, A k) := Set.disjoint_iUnion₂_right.mpr hid
  have hcrossU : ∀ a ∈ A i, ∀ b ∈ (⋃ k ∈ s, A k), U a b = 0 := by
    intro a ha b hb
    obtain ⟨k,hk,hbk⟩ := mem_iUnion₂.mp hb
    exact hcross i (Finset.mem_insert_self _ _) k (Finset.mem_insert_of_mem hk)
      (fun hh => hi (hh ▸ hk)) a ha b hbk
  have hp : (∀ k ∈ insert i s, occupation (A k) x = (n k : ℝ)) ↔
      Fintype.card {j : ι // j ∈ r} = n i ∧
        ∀ k ∈ s, occupation (A k) (fun j : {j : ι // j ∉ r} => x j) = (n k : ℝ) := by
    rw [Finset.forall_mem_insert, occupation_binary_left hdU r hx]
    simp only [Nat.cast_inj]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro k
    apply forall_congr'
    intro hk
    rw [occupation_binary_right (hid k hk) r hx]
  unfold fixedOccupationFamily countFamily
  simp only [hp, gibbsFamily_binary_eq hU β h hdU hcrossU r hx]
  split_ifs <;> simp_all

theorem grandIntegral_fixedOccupation_product {κ : Type u_1}
    {U : Space → Space → ℝ} (hm : Measurable (Function.uncurry U))
    (hU : ∀ x y, U x y = U y x) (β h : ℝ)
    (A : κ → Set Space) (n : κ → ℕ) (s : Finset κ)
    (hA : ∀ k ∈ s, MeasurableSet (A k))
    (hd : (s : Set κ).Pairwise (fun j k => Disjoint (A j) (A k)))
    (hcross : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → ∀ a ∈ A j, ∀ b ∈ A k, U a b = 0)
    (hF : GrandFinite (gibbsFamily U β h) (⋃ k ∈ s, A k)) :
    grandIntegral (fixedOccupationFamily A s n (gibbsFamily U β h)) (⋃ k ∈ s, A k) =
      ∏ k ∈ s, familyTerm (gibbsFamily U β h) (A k) (n k) := by
  induction s using Finset.induction_on with
  | empty =>
    have he : fixedOccupationFamily A ∅ n (gibbsFamily U β h) = gibbsFamily U β h := by
      funext ι inst x
      simp [fixedOccupationFamily]
    rw [he]
    simpa using grandIntegral_gibbs_empty U β h
  | @insert i s hi ih =>
    have hAi := hA i (Finset.mem_insert_self _ _)
    have hAs (k : κ) (hk : k ∈ s) := hA k (Finset.mem_insert_of_mem hk)
    have hB : MeasurableSet (⋃ k ∈ s, A k) := MeasurableSet.biUnion s.finite_toSet.countable hAs
    have hdU : Disjoint (A i) (⋃ k ∈ s, A k) := by
      apply Set.disjoint_iUnion₂_right.mpr
      intro k hk
      exact hd (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hk) (fun hh => hi (hh ▸ hk))
    have hfi := hF.mono_set (subset_iUnion₂_of_subset i (Finset.mem_insert_self i s) Subset.rfl)
      (gibbsFamily_nonneg U β h)
    have hfs := hF.mono_set (iUnion₂_subset (fun k hk =>
      subset_iUnion₂_of_subset k (Finset.mem_insert_of_mem hk) Subset.rfl)) (gibbsFamily_nonneg U β h)
    have hmF := measurable_gibbsFamily hm β h
    have hfull := hF.fixedOccupation n hA (fun ι _ => hmF ι) (gibbsFamily_nonneg U β h)
    have htail := hfs.fixedOccupation n hAs (fun ι _ => hmF ι) (gibbsFamily_nonneg U β h)
    have hbin := grandIntegral_product_eq
      (fixedOccupationFamily A (insert i s) n (gibbsFamily U β h))
      (countFamily (gibbsFamily U β h) (n i))
      (fixedOccupationFamily A s n (gibbsFamily U β h))
      (countFamily_relabel _ (gibbsFamily_relabel U β h) (n i))
      (fixedOccupationFamily_relabel A s n _ (gibbsFamily_relabel U β h))
      hAi hB hdU (by simpa only [Finset.set_biUnion_insert] using hfull) (hfi.count (n i)) htail
      (fun _ r x hx => fixedOccupation_binary_eq A n hi hd hU β h hcross r hx)
    rw [Finset.set_biUnion_insert, hbin, grandIntegral_countFamily, Finset.prod_insert hi]
    rw [ih hAs (hd.mono (Finset.subset_insert _ _))
      (fun j hj k hk => hcross j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)) hfs]

end ContinuumTemperature
end

end OAI
