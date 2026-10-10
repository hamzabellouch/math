import OAI.NumberTheory.ShortEgyptian.Basic

namespace OAI

namespace ShortEgyptian

theorem exists_expansion (a b : ℕ) (hab : a < b) :
    ∃ ns : List ℕ, IsExpansion a b ns := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha0 : a = 0
    · subst a
      exact ⟨[], by simp [IsExpansion]⟩
    have ha : 0 < a := Nat.pos_of_ne_zero ha0
    have hb : 0 < b := lt_trans ha hab
    have haQ : (0 : ℚ) < a := by exact_mod_cast ha
    have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
    let z := quotient b a
    let r := residue b a z
    have hz : 0 < z := (quotient_spec hb ha).1
    have hzQ : (0 : ℚ) < z := by exact_mod_cast hz
    have hz2 : 2 ≤ z := by
      change 2 ≤ ⌈(b : ℚ) / a⌉₊
      apply Nat.succ_le_of_lt
      apply Nat.lt_ceil.mpr
      norm_num only [Nat.cast_one]
      apply (lt_div_iff₀ haQ).mpr
      simpa using (show (a : ℚ) < b by exact_mod_cast hab)
    have hrlt : r < a := (residue_spec hb ha).1
    have hre : b + r = a * z := (residue_spec hb ha).2
    have hbz : b ≤ b * z := by nlinarith
    have hrbz : r < b * z := lt_of_lt_of_le (lt_trans hrlt hab) hbz
    obtain ⟨ns, hns⟩ := ih r hrlt (b * z) hrbz
    rw [isExpansion_iff] at hns
    have hnseq : unitSum ns = (r : ℚ) / (b * z : ℕ) := hns.2.2
    have hrQ : (r : ℚ) < b := by exact_mod_cast (lt_trans hrlt hab)
    have hsmall : unitSum ns < (1 : ℚ) / z := by
      rw [hnseq, Nat.cast_mul]
      apply (div_lt_div_iff₀ (mul_pos hbQ hzQ) hzQ).mpr
      nlinarith
    have horder : ∀ n ∈ ns, z < n := by
      intro n hn
      have hn2 := hns.2.1 n hn
      have hnQ : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
      by_contra h
      have hnz : (n : ℚ) ≤ z := by exact_mod_cast (Nat.le_of_not_gt h)
      have hdiv := one_div_le_one_div_of_le hnQ hnz
      have hsum := unit_le_sum hn
      linarith
    refine ⟨z :: ns, ?_⟩
    rw [isExpansion_iff]
    refine ⟨(List.pairwise_cons.mpr ⟨horder, hns.1⟩), ?_, ?_⟩
    · intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact hz2
      · exact hns.2.1 n hn
    · change (1 : ℚ) / z + unitSum ns = (a : ℚ) / b
      rw [hnseq, Nat.cast_mul]
      have heq : (b : ℚ) + r = a * z := by exact_mod_cast hre
      field_simp
      nlinarith

theorem minLength_attained {a b : ℕ} (hab : a < b) :
    ∃ ns : List ℕ, IsExpansion a b ns ∧ ns.length = minLength a b := by
  obtain ⟨ns, hns⟩ := exists_expansion a b hab
  have hex : {k : ℕ | ∃ ns : List ℕ, IsExpansion a b ns ∧ ns.length = k}.Nonempty :=
    ⟨ns.length, ns, hns, rfl⟩
  exact Nat.sInf_mem hex

theorem minLength_le {a b : ℕ} {ns : List ℕ} (hns : IsExpansion a b ns) :
    minLength a b ≤ ns.length := Nat.sInf_le ⟨ns, hns, rfl⟩

theorem minLength_le_maxMinLength {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    minLength a b ≤ maxMinLength b := by
  unfold maxMinLength
  exact Finset.le_sup (f := fun a : ℕ => minLength a b) (Finset.mem_Ico.mpr ⟨ha, hab⟩)

end ShortEgyptian

end OAI
