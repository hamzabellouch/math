import OAI.Probability.ContinuumTransition.ProductEquality

namespace OAI

universe u_1

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gibbsFamily_binary_le {U : Space → Space → ℝ} (hU : ∀ x y, U x y = U y x)
    {β h : ℝ} (hβ : 0 ≤ β) {A B : Set Space}
    (hcross : ∀ x ∈ A, ∀ y ∈ B, 0 ≤ U x y)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : Finset ι) {x : ι → Space} (hx : x ∈ binaryRegion A B s) :
    gibbsFamily U β h ι x ≤ gibbsFamily U β h {i : ι // i ∈ s} (fun i => x i)*
      gibbsFamily U β h {i : ι // i ∉ s} (fun i => x i) := by
  by_cases hinj : Function.Injective x
  · have hi : Function.Injective (fun i : {i : ι // i ∈ s} => x i) := hinj.comp Subtype.val_injective
    have hj : Function.Injective (fun i : {i : ι // i ∉ s} => x i) := hinj.comp Subtype.val_injective
    simp only [gibbsFamily, ite_eq_left hinj, ite_eq_left hi, ite_eq_left hj, ← Real.exp_add, Real.exp_le_exp]
    have he : gibbsEnergy U x = gibbsEnergy U (fun i : {i : ι // i ∈ s} => x i)+
        gibbsEnergy U (fun i : {i : ι // i ∉ s} => x i)+
        ∑ i : {i : ι // i ∈ s}, ∑ j : {j : ι // j ∉ s}, U (x i) (x j) := by
      convert gibbsEnergy_split U hU (fun i => i ∈ s) x using 1
      congr! 5
    have hc : (Fintype.card {i : ι // i ∈ s} : ℝ)+Fintype.card {i : ι // i ∉ s} = Fintype.card ι := by
      have hh := Fintype.card_subtype_compl (fun i : ι => i ∈ s)
      have hl := Fintype.card_subtype_le (fun i : ι => i ∈ s)
      have he : Fintype.card {i : ι // i ∈ s}+Fintype.card {i : ι // i ∉ s} = Fintype.card ι := by omega
      exact_mod_cast he
    have hz : 0 ≤ ∑ i : {i : ι // i ∈ s}, ∑ j : {i : ι // i ∉ s}, U (x i) (x j) := by
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro j _
      exact hcross (x i) (by simpa only [ite_eq_left i.property] using hx i)
        (x j) (by simpa only [ite_eq_right j.property] using hx j)
    rw [he, ← hc]
    nlinarith only [mul_nonneg hβ hz]
  · rw [gibbsFamily, ite_eq_right hinj]
    exact mul_nonneg (gibbsFamily_nonneg _ _ _ _ _) (gibbsFamily_nonneg _ _ _ _ _)

theorem grandIntegral_gibbs_empty (U : Space → Space → ℝ) (β h : ℝ) :
    grandIntegral (gibbsFamily U β h) ∅ = 1 := by
  rw [grandIntegral, tsum_eq_single 0, gibbsFamily_term_zero]
  intro n hn
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  have he : {x : Fin n → Space | ∀ i, x i ∈ (∅ : Set Space)} = ∅ := by
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall]
    exact ⟨⟨0, hn'⟩, not_false⟩
  simp only [familyTerm, familyIntegral, he, setIntegral_empty, zero_div]

theorem grandIntegral_gibbs_blocks {κ : Type u_1} {U : Space → Space → ℝ}
    (hU : ∀ x y, U x y = U y x) {β h : ℝ} (hβ : 0 ≤ β)
    (A : κ → Set Space) (s : Finset κ)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hd : (s : Set κ).Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, 0 ≤ U x y)
    (hF : GrandFinite (gibbsFamily U β h) (⋃ i ∈ s, A i)) :
    grandIntegral (gibbsFamily U β h) (⋃ i ∈ s, A i) ≤
      ∏ i ∈ s, grandIntegral (gibbsFamily U β h) (A i) := by
  induction s using Finset.induction_on with
  | empty => simp [grandIntegral_gibbs_empty]
  | @insert i s hi ih =>
    let B := ⋃ j ∈ s, A j
    have hB : MeasurableSet B := MeasurableSet.biUnion s.finite_toSet.countable
      (fun j hj => hA j (Finset.mem_insert_of_mem hj))
    have hAi := hA i (Finset.mem_insert_self _ _)
    have hAB : Disjoint (A i) B := by
      apply Set.disjoint_iUnion₂_right.mpr
      intro j hj
      exact hd (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj) (fun h => hi (h ▸ hj))
    have he : (⋃ j ∈ insert i s, A j) = A i ∪ B := by simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, B]
    rw [he] at hF ⊢
    have hFi := hF.mono_set subset_union_left (gibbsFamily_nonneg U β h)
    have hFB := hF.mono_set subset_union_right (gibbsFamily_nonneg U β h)
    have hb := grandIntegral_product_bound (gibbsFamily U β h) (gibbsFamily U β h) (gibbsFamily U β h)
      (gibbsFamily_relabel U β h) (gibbsFamily_relabel U β h) hAi hB hAB hF hFi hFB ?_
    swap
    · intro n r x hx
      apply gibbsFamily_binary_le hU hβ ?_ r hx
      intro a ha b hb
      obtain ⟨j, hj, hjb⟩ := mem_iUnion₂.mp hb
      exact hcross i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun hh => hi (hh ▸ hj)) a ha b hjb
    have ih' := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      (hd.mono (Finset.subset_insert _ _))
      (fun j hj k hk => hcross j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)) hFB
    rw [Finset.prod_insert hi]
    exact hb.trans (mul_le_mul_of_nonneg_left ih' (tsum_nonneg
      (familyTerm_nonneg _ _ (gibbsFamily_nonneg U β h))))

end ContinuumTemperature
end

end OAI
