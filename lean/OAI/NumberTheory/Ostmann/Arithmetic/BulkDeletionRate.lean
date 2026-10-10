import OAI.NumberTheory.Ostmann.Arithmetic.BulkDeletionCost

namespace OAI

/-! # Uniform decay of the original deletion and collision costs -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

private theorem bulk_auxiliary_prefactor_le (C L a d H B : ℝ)
    (hC : 1 ≤ C) (hL : 1 ≤ L) (ha0 : 0 ≤ a) (hd0 : 0 ≤ d) (_hB0 : 0 ≤ B)
    (ha : a ≤ C * L) (hd : d ≤ Real.exp (C * L)) (hH : H ≤ C * L)
    (hB : B ≤ Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L))) :
    B * (a ^ 2 + 2 * a * d) * Real.exp H ≤
      Real.exp (6 * C * L ^ 2 + 6 * C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
  have hC0 : 0 ≤ C := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hae : a ≤ Real.exp (C * L) := ha.trans (by linarith [Real.add_one_le_exp (C * L)])
  have hpoly : a ^ 2 + 2 * a * d ≤ 3 * Real.exp (2 * C * L) := by
    have hsq := pow_le_pow_left₀ ha0 hae 2
    have had := mul_le_mul hae hd hd0 (Real.exp_nonneg _)
    rw [← Real.exp_nat_mul] at hsq
    have hsq' : a ^ 2 ≤ Real.exp (2 * C * L) := by
      convert hsq using 1
      congr 1
      ring
    rw [← Real.exp_add] at had
    have he : C * L + C * L = 2 * C * L := by ring
    rw [he] at had
    nlinarith [hsq']
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
  calc
    _ ≤ Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) *
        (3 * Real.exp (2 * C * L)) * Real.exp (C * L) := by
      gcongr
    _ ≤ Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) *
        (Real.exp 2 * Real.exp (2 * C * L)) * Real.exp (C * L) := by gcongr
    _ ≤ _ := by
      simp only [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hLsq : L ≤ L ^ 2 := by nlinarith
      have hCLsq : 1 ≤ C * L ^ 2 := by nlinarith
      have he : 0 ≤ C * L * Real.exp ((1 / 1000 : ℝ) * L) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hLsq hC0]

/-- The cutoff precedes the bulk dimension, deletion sets, and original
normalizers. Both bad-event costs have a stronger saving than the cell error. -/
theorem bulk_collision_deletion_numerical_rate (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ a d H T B : ℝ,
      0 ≤ a → 0 ≤ d → 0 ≤ B → a ≤ C * L → d ≤ Real.exp (C * L) → H ≤ C * L →
      B ≤ Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) →
      Real.exp ((39 / 10000 : ℝ) * L) ≤ T →
      a * d * Real.exp (H - T) ≤ Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) ∧
      B * (a ^ 2 + 2 * a * d) * Real.exp (H - T) ≤
        Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  filter_upwards [arithmetic_error_absorption (1 / 1000) (39 / 10000) (2 / 1000)
    (6 * C) 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro a d H T B ha0 hd0 hB0 ha hd hH hB hT
  have hB1 : (1 : ℝ) ≤ Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) :=
    Real.one_le_exp_iff.mpr (by
      have : 0 ≤ C := by linarith
      have : 0 ≤ L := by linarith
      positivity)
  have hp := bulk_auxiliary_prefactor_le C L a d H B hC hL ha0 hd0 hB0 ha hd hH hB
  have hp1 := bulk_auxiliary_prefactor_le C L a d H 1 hC hL ha0 hd0 (by norm_num) ha hd hH hB1
  have hmass : a * d * Real.exp H ≤
      Real.exp (6 * C * L ^ 2 + 6 * C * L * Real.exp ((1 / 1000 : ℝ) * L)) := by
    apply le_trans _ hp1
    simp only [one_mul]
    exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg ha0 hd0]) (Real.exp_nonneg _)
  have he : Real.exp (-T) ≤ Real.exp (-Real.exp ((39 / 10000 : ℝ) * L)) :=
    Real.exp_le_exp.mpr (neg_le_neg hT)
  have hfinish (b : ℝ) (_hb0 : 0 ≤ b)
      (hb : b * Real.exp H ≤ Real.exp
        (6 * C * L ^ 2 + 6 * C * L * Real.exp ((1 / 1000 : ℝ) * L))) :
      b * Real.exp (H - T) ≤ Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
    rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg, ← mul_assoc]
    exact (mul_le_mul hb he (Real.exp_nonneg _) (Real.exp_nonneg _)).trans (by
      simpa only [one_mul, neg_mul] using hrate)
  exact ⟨hfinish (a * d) (mul_nonneg ha0 hd0) hmass,
    hfinish (B * (a ^ 2 + 2 * a * d)) (by positivity) hp⟩

/-- The actual deleted-set expression, with all old normalizers, and the
distinctness error are absorbed together. -/
theorem bulk_collision_deletion_rate (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (J : Type) [Fintype J] (S D : J → Finset ℕ)
      (Z : J → ℝ) (H T K B : ℝ),
      (∀ j, 0 ≤ Z j) → (∀ j, Z j ≤ Real.exp H) →
      (∀ j, ((D j).card : ℝ) ≤ K) → 0 ≤ K → 0 ≤ B →
      (Fintype.card J : ℝ) ≤ C * L → K ≤ Real.exp (C * L) → H ≤ C * L →
      B ≤ Real.exp (C * L ^ 2 + C * L * Real.exp ((1 / 1000 : ℝ) * L)) →
      Real.exp ((39 / 10000 : ℝ) * L) ≤ T →
      (∀ j q, q ∈ S j → Real.exp T ≤ (q : ℝ)) →
      B * (Fintype.card J : ℝ) ^ 2 * Real.exp (H - T) +
        B * ((∏ j, (1 + Z j * ∑ q ∈ S j ∩ D j, (q : ℝ)⁻¹)) - 1) ≤
      Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  filter_upwards [bulk_collision_deletion_numerical_rate C hC] with L hrate
  intro J _ S D Z H T K B hZ0 hZ hcard hK hB0 hJ hKbound hH hB hT hlow
  have hb := hrate (Fintype.card J) K H T B (Nat.cast_nonneg _) hK hB0 hJ hKbound hH hB hT
  have hsmall : (Fintype.card J : ℝ) * K * Real.exp (H - T) ≤ 1 :=
    hb.1.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_nonneg _)))
  have hd := bulk_deleted_product_cost S D Z H T K hZ0 hZ hcard hlow hsmall
  apply le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hd hB0)) _
  calc
    _ = B * ((Fintype.card J : ℝ) ^ 2 + 2 * (Fintype.card J : ℝ) * K) * Real.exp (H - T) := by ring
    _ ≤ _ := hb.2

end Ostmann

end OAI
