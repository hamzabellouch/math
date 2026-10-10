import OAI.NumberTheory.Ostmann.Preliminaries.Stability
import OAI.NumberTheory.Ostmann.Supply.LogImbalanceVariance
import OAI.NumberTheory.Ostmann.Preliminaries.PrimeReciprocalLogBudget

namespace OAI

/-! # The actual complementary-support imbalance is controlled by collisions -/

namespace Ostmann
open scoped Classical BigOperators

theorem supportRatio_variance_le_defect (p : ℕ) (S T : Finset ℕ)
    (μ ν : ℕ → ℝ) (hS : S.Nonempty) (hT : T.Nonempty)
    (hcard : S.card + T.card = p) :
    ((T.card : ℝ) / S.card) + ((T.card : ℝ) / S.card)⁻¹ - 2 ≤
      (p : ℝ) * collisionDefect p S T μ ν := by
  have hSc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hTc : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hcr : (S.card : ℝ) + T.card = p := by exact_mod_cast hcard
  have hp : (0 : ℝ) < p := by linarith
  have he : ((T.card : ℝ) / S.card) + ((T.card : ℝ) / S.card)⁻¹ - 2 =
      (p : ℝ) * (1 / (S.card : ℝ) + 1 / (T.card : ℝ) - 4 / (p : ℝ)) := by
    rw [inv_div]
    field_simp
    nlinarith
  rw [he]
  apply mul_le_mul_of_nonneg_left _ hp.le
  unfold collisionDefect
  have h1 : 0 ≤ ∑ r ∈ S, (μ r - 1 / (S.card : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : 0 ≤ ∑ r ∈ T, (ν r - 1 / (T.card : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

theorem collision_logarithmic_imbalance {C : ℝ} (hM : MertensEstimate C)
    (Q : ℕ) (P : Finset ℕ) (hP : P ⊆ Nat.primesLE Q)
    (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ)
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card = p)
    (D : ℝ) (hD : (∑ p ∈ P, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ D) :
    (∑ p ∈ P, |Real.log ((T p).card / ((S p).card : ℝ))| / p) ^ 2 ≤
      4 * D * primeReciprocalLogConstant C := by
  let κ := fun p => ((T p).card : ℝ) / (S p).card
  have hprime (p) (hp : p ∈ P) := Nat.prime_of_mem_primesLE (hP hp)
  have hκ (p) (hp : p ∈ P) : 0 < κ p := by
    exact div_pos (by exact_mod_cast (hT p hp).card_pos)
      (by exact_mod_cast (hS p hp).card_pos)
  let V := ∑ p ∈ P, (κ p + (κ p)⁻¹ - 2) * Real.log p / p
  let J := ∑ p ∈ P, 1 / ((p : ℝ) * Real.log p)
  have hV0 : 0 ≤ V := by
    apply Finset.sum_nonneg
    intro p hp
    have hv : 0 ≤ κ p + (κ p)⁻¹ - 2 := by
      nlinarith [log_sq_le_four_variance (κ p) (hκ p hp), sq_nonneg (Real.log (κ p))]
    positivity
  have hV : V ≤ D := by
    apply le_trans _ hD
    apply Finset.sum_le_sum
    intro p hp
    have hpp : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    have hl : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
    have hh := supportRatio_variance_le_defect p (S p) (T p) (μ p) (ν p)
      (hS p hp) (hT p hp) (hcard p hp)
    have hm := mul_le_mul_of_nonneg_right hh (div_nonneg hl hpp.le)
    dsimp [κ]
    convert hm using 1 <;> field_simp
  have hJ0 : 0 ≤ J := by
    apply Finset.sum_nonneg
    intro p _
    exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
  have hJ : J ≤ primeReciprocalLogConstant C := by
    apply le_trans _ (primeReciprocalLogSum_uniform hM Q)
    exact Finset.sum_le_sum_of_subset_of_nonneg hP (fun p _ _ =>
      one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)))
  have hh := logarithmic_imbalance_budget P κ (fun p hp => (hprime p hp).one_lt) hκ
  apply hh.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left hV (by norm_num)) hJ hJ0
    (mul_nonneg (by norm_num) (hV0.trans hV))

end Ostmann

end OAI
