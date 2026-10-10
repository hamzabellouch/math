import OAI.NumberTheory.Ostmann.Construction.OriginalParameterChoice

namespace OAI

/-! # Product and frequency ranges for the concrete moment parameters -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubsetProducts_log_bounds (P : Finset ℕ) (k z M : ℕ)
    (hz : 0 < z) (hP : ∀ p ∈ P, p.Prime)
    (hrange : ∀ p ∈ P, z ≤ p ∧ p ≤ 2 * z) (hM : M ∈ primeSubsetProducts P k) :
    (k : ℝ) * Real.log z ≤ Real.log (M : ℝ) ∧
      Real.log (M : ℝ) ≤ (k : ℝ) * (Real.log z + Real.log 2) := by
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hM
  obtain ⟨hQP, hcard⟩ := Finset.mem_powersetCard.mp hQ
  have hlog : Real.log ((∏ p ∈ Q, p : ℕ) : ℝ) = ∑ p ∈ Q, Real.log (p : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (hP p (hQP hp)).ne_zero
  rw [hlog]
  constructor
  · have hh := Finset.sum_le_sum (s := Q) (fun (p : ℕ) hp =>
      Real.log_le_log (show (0 : ℝ) < z by exact_mod_cast hz)
        (show (z : ℝ) ≤ p by exact_mod_cast (hrange p (hQP hp)).1))
    simpa only [Finset.sum_const, nsmul_eq_mul, hcard] using hh
  · have hh := Finset.sum_le_sum (s := Q) (fun (p : ℕ) hp =>
      Real.log_le_log (show (0 : ℝ) < p by exact_mod_cast (hP p (hQP hp)).pos)
        (show (p : ℝ) ≤ 2 * z by exact_mod_cast (hrange p (hQP hp)).2))
    have hz0 : (z : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hz)
    rw [Real.log_mul (by norm_num) hz0] at hh
    simpa only [Finset.sum_const, nsmul_eq_mul, hcard, add_comm] using hh

theorem original_prime_product_scale (P : Finset ℕ) (z : ℕ) (L V : ℝ)
    (hz : 0 < z) (hV : 0 < V) (hLV : Real.log (z : ℝ) = V) (hL : 0 ≤ L)
    (hP : ∀ p ∈ P, p.Prime) (hrange : ∀ p ∈ P, z ≤ p ∧ p ≤ 2 * z)
    (hklog : (originalMomentOrder L V : ℝ) * Real.log 2 ≤ V) :
    ∀ M ∈ primeSubsetProducts P (originalMomentOrder L V),
      Real.exp (10 * V) ≤ (M : ℝ) / Real.exp L ∧
      (M : ℝ) / Real.exp L ≤ Real.exp (13 * V) := by
  intro M hM
  have hb := primeSubsetProducts_log_bounds P (originalMomentOrder L V) z M hz hP hrange hM
  rw [hLV] at hb
  have hMpos : 0 < M := by
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hM
    exact Finset.prod_pos (fun p hp => (hP p ((Finset.mem_powersetCard.mp hQ).1 hp)).pos)
  have hratio : 0 < (M : ℝ) / Real.exp L := div_pos (by exact_mod_cast hMpos) (Real.exp_pos _)
  obtain ⟨hk, hlo, hhi⟩ := originalMomentOrder_scale L V hL hV
  have hsub : ((originalMomentOrder L V - 10 : ℕ) : ℝ) = (originalMomentOrder L V : ℝ) - 10 := by
    rw [Nat.cast_sub hk]; norm_num
  rw [hsub] at hlo
  constructor
  · apply (Real.le_log_iff_exp_le hratio).mp
    rw [Real.log_div (by exact_mod_cast (Nat.ne_of_gt hMpos)) (Real.exp_ne_zero _), Real.log_exp]
    nlinarith only [hb.1, hlo]
  · apply (Real.log_le_iff_le_exp hratio).mp
    rw [Real.log_div (by exact_mod_cast (Nat.ne_of_gt hMpos)) (Real.exp_ne_zero _), Real.log_exp]
    nlinarith only [hb.2, hhi, hklog]

theorem originalFrequencyCutoff_bounds (V : ℝ) (hV : 2 ≤ V) :
    1 ≤ originalFrequencyCutoff V ∧ (originalFrequencyCutoff V : ℝ) ≤ Real.exp (14 * V) := by
  have hpos : 0 < Real.exp (27 * V / 2) := Real.exp_pos _
  refine ⟨(Nat.one_le_ceil_iff).mpr hpos, ?_⟩
  have hceil := (Nat.ceil_lt_add_one hpos.le).le
  have he : 1 ≤ Real.exp (27 * V / 2) := Real.one_le_exp (by linarith)
  have h2 : 2 ≤ Real.exp (V / 2) := by linarith [Real.add_one_le_exp (V / 2)]
  have hh := mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg (27 * V / 2))
  have heq : Real.exp (27 * V / 2) * Real.exp (V / 2) = Real.exp (14 * V) := by
    rw [← Real.exp_add]; congr 1; ring
  change (originalFrequencyCutoff V : ℝ) ≤ _
  change (⌈Real.exp (27 * V / 2)⌉₊ : ℝ) ≤ _
  rw [heq] at hh
  linarith

theorem originalFrequencyCutoff_covers (V B R Q : ℝ)
    (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hRU : R ≤ Real.exp (13 * V))
    (hQU : Q ≤ Real.exp (V / 50)) (hB : B ^ 2 ≤ Real.exp (12 * V / 25)) :
    B ^ 2 * R * Q ≤ (originalFrequencyCutoff V : ℝ) := by
  apply le_trans _ (Nat.le_ceil (Real.exp (27 * V / 2)))
  have hh := mul_le_mul (mul_le_mul hB hRU hR (Real.exp_nonneg _)) hQU hQ
    (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
  have heq : Real.exp (12 * V / 25) * Real.exp (13 * V) * Real.exp (V / 50) =
      Real.exp (27 * V / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  exact heq ▸ hh

end Ostmann

end OAI
