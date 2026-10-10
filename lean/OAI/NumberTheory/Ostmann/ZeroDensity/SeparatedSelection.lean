import Mathlib

namespace OAI

namespace Ostmann.ZeroDensity
open scoped BigOperators

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

theorem neighbor_card_le_two_local (s : Finset ι) (c : ι → κ) (γ : ι → ℝ) (j : ι)
    {B : ℝ}
    (hlocal : ∀ χ t, ((s.filter (fun i => c i = χ ∧ |γ i - t| ≤ 1 / 2)).card : ℝ) ≤ B) :
    ((s.filter (fun i => c i = c j ∧ |γ i - γ j| < 1)).card : ℝ) ≤ 2 * B := by
  classical
  let L := s.filter (fun i => c i = c j ∧ |γ i - (γ j - 1 / 2)| ≤ 1 / 2)
  let R := s.filter (fun i => c i = c j ∧ |γ i - (γ j + 1 / 2)| ≤ 1 / 2)
  have hsub : s.filter (fun i => c i = c j ∧ |γ i - γ j| < 1) ⊆ L ∪ R := by
    intro i hi
    obtain ⟨his, hic, hid⟩ := Finset.mem_filter.mp hi
    have hd := abs_lt.mp hid
    by_cases hleft : γ i ≤ γ j
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_filter.mpr
      exact ⟨his, hic, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      exact ⟨his, hic, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hcard : ((s.filter (fun i => c i = c j ∧ |γ i - γ j| < 1)).card : ℝ) ≤
      (L.card : ℝ) + R.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le L R)
  have hL : (L.card : ℝ) ≤ B := hlocal (c j) (γ j - 1 / 2)
  have hR : (R.card : ℝ) ≤ B := hlocal (c j) (γ j + 1 / 2)
  linarith

theorem exists_separated_cover (s : Finset ι) (c : ι → κ) (γ : ι → ℝ) :
    ∃ r : Finset ι, r ⊆ s ∧
      (∀ i ∈ r, ∀ j ∈ r, i ≠ j → c i = c j → 1 ≤ |γ i - γ j|) ∧
      ∀ i ∈ s, ∃ j ∈ r, c i = c j ∧ |γ i - γ j| < 1 := by
  classical
  let good : Finset (Finset ι) := s.powerset.filter (fun r =>
    ∀ i ∈ r, ∀ j ∈ r, i ≠ j → c i = c j → 1 ≤ |γ i - γ j|)
  have hgood : good.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [good]
  obtain ⟨r, hr, hmax⟩ := Finset.exists_max_image good Finset.card hgood
  obtain ⟨hrs, hsep⟩ := Finset.mem_filter.mp hr
  have hsub : r ⊆ s := Finset.mem_powerset.mp hrs
  refine ⟨r, hsub, hsep, ?_⟩
  intro i his
  by_contra hcover
  have hin : i ∉ r := by
    intro hir
    exact hcover ⟨i, hir, rfl, by norm_num⟩
  have hpair : ∀ j ∈ r, c i = c j → 1 ≤ |γ i - γ j| := by
    intro j hj hc
    by_contra hd
    exact hcover ⟨j, hj, hc, lt_of_not_ge hd⟩
  have hnew : insert i r ∈ good := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset his hsub), ?_⟩
    intro a ha b hb hab hc
    rcases Finset.mem_insert.mp ha with hai | har
    · rcases Finset.mem_insert.mp hb with hbi | hbr
      · subst a
        subst b
        exact (hab rfl).elim
      · subst a
        exact hpair b hbr hc
    · rcases Finset.mem_insert.mp hb with hbi | hbr
      · subst b
        simpa only [abs_sub_comm] using hpair a har hc.symm
      · exact hsep a har b hbr hab hc
  have hcard := hmax (insert i r) hnew
  rw [Finset.card_insert_of_notMem hin] at hcard
  omega

theorem exists_separated_selection (s : Finset ι) (c : ι → κ) (γ : ι → ℝ) {B : ℝ}
    (hlocal : ∀ χ t, ((s.filter (fun i => c i = χ ∧ |γ i - t| ≤ 1 / 2)).card : ℝ) ≤ B) :
    ∃ r : Finset ι, r ⊆ s ∧
      (∀ i ∈ r, ∀ j ∈ r, i ≠ j → c i = c j → 1 ≤ |γ i - γ j|) ∧
      (s.card : ℝ) ≤ 2 * B * r.card := by
  classical
  obtain ⟨r, hrs, hsep, hcover⟩ := exists_separated_cover s c γ
  refine ⟨r, hrs, hsep, ?_⟩
  let U : ι → Finset ι := fun j => s.filter (fun i => c i = c j ∧ |γ i - γ j| < 1)
  have hsub : s ⊆ r.biUnion U := by
    intro i hi
    obtain ⟨j, hj, hic, hid⟩ := hcover i hi
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨hi, hic, hid⟩⟩
  have hcount : (s.card : ℝ) ≤ ∑ j ∈ r, ((U j).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  calc
    (s.card : ℝ) ≤ ∑ j ∈ r, ((U j).card : ℝ) := hcount
    _ ≤ ∑ _j ∈ r, 2 * B := Finset.sum_le_sum (fun j _ => neighbor_card_le_two_local s c γ j hlocal)
    _ = 2 * B * r.card := by simp [mul_comm]

end Ostmann.ZeroDensity

end OAI
