import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

def dyadicMagnitudeBand (k : ℕ) (z : ℝ) : Prop :=
  (1 / 2 : ℝ) ^ (k + 1) < z ∧ z ≤ (1 / 2 : ℝ) ^ k

theorem half_pow_antitone : Antitone (fun k : ℕ => (1 / 2 : ℝ) ^ k) := by
  apply antitone_nat_of_succ_le
  intro k
  rw [pow_succ]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k]

theorem dyadicMagnitudeBand_exists {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    ∃ k : ℕ, dyadicMagnitudeBand k z :=
  exists_nat_pow_near_of_lt_one hz hz1 (by norm_num) (by norm_num)

theorem dyadicMagnitudeBand_unique {k l : ℕ} {z : ℝ}
    (hk : dyadicMagnitudeBand k z) (hl : dyadicMagnitudeBand l z) : k = l := by
  have hkl : ¬k < l := by
    intro h
    have hs := half_pow_antitone (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hl.2.trans hs)) hk.1
  have hlk : ¬l < k := by
    intro h
    have hs := half_pow_antitone (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hk.2.trans hs)) hl.1
  omega

theorem dyadicMagnitudeBand_pos {k : ℕ} {z : ℝ}
    (hk : dyadicMagnitudeBand k z) : 0 < z :=
  (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (k + 1)).trans hk.1

theorem finite_dyadicMagnitudeBand_cutoff {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, w i ≤ 1) :
    ∃ K : ℕ, ∀ i, 0 < w i → ∃ k ≤ K, dyadicMagnitudeBand k (w i) := by
  let band : ι → ℕ := fun i =>
    if h : 0 < w i then Classical.choose (dyadicMagnitudeBand_exists h (hw i)) else 0
  refine ⟨Finset.univ.sup band, ?_⟩
  intro i hi
  refine ⟨band i, Finset.le_sup (Finset.mem_univ i), ?_⟩
  simp only [band, dite_eq_left hi]
  exact Classical.choose_spec (dyadicMagnitudeBand_exists hi (hw i))

theorem dyadicMagnitudeBand_card_lt {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i ≤ 1) (k : ℕ) :
    (s.filter (fun i => dyadicMagnitudeBand k (w i))).card < 2 ^ (k + 1) := by
  classical
  let u := s.filter (fun i => dyadicMagnitudeBand k (w i))
  by_contra hnot
  have hcard : 2 ^ (k + 1) ≤ u.card := Nat.le_of_not_gt hnot
  have hcardpos : 0 < u.card := (pow_pos (by decide : (0 : ℕ) < 2) (k + 1)).trans_le hcard
  have hu : u.Nonempty := Finset.card_pos.mp hcardpos
  have hlt : (∑ i ∈ u, (1 / 2 : ℝ) ^ (k + 1)) < ∑ i ∈ u, w i :=
    Finset.sum_lt_sum_of_nonempty hu (fun i hi => (Finset.mem_filter.mp hi).2.1)
  have hsumu : (∑ i ∈ u, w i) ≤ 1 := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i hi _ => hw i hi)) hsum
  have hcardreal : (2 : ℝ) ^ (k + 1) ≤ (u.card : ℝ) := by exact_mod_cast hcard
  have hmul := mul_le_mul_of_nonneg_right hcardreal
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (k + 1))
  have hunit : (2 : ℝ) ^ (k + 1) * (1 / 2 : ℝ) ^ (k + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hunit] at hmul
  have hleft : (∑ i ∈ u, (1 / 2 : ℝ) ^ (k + 1)) =
      (u.card : ℝ) * (1 / 2 : ℝ) ^ (k + 1) := by simp
  rw [hleft] at hlt
  linarith

theorem norm_le_band_bound {E : Type*} [NormedAddCommGroup E]
    {a : ℝ} (ha : 0 < a) {k : ℕ} {x : E}
    (hx : dyadicMagnitudeBand k (‖x‖ ^ a)) :
    ‖x‖ ≤ ((1 / 2 : ℝ) ^ k) ^ (1 / a) := by
  have h := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg x) a) hx.2
    (one_div_nonneg.mpr ha.le)
  simpa only [one_div, Real.rpow_rpow_inv (norm_nonneg x) ha.ne'] using h

def bandGeometricRatio (a r : ℝ) : ℝ :=
  (2 : ℝ) ^ (1 / r) * (1 / 2 : ℝ) ^ (1 / a)

theorem bandGeometricRatio_pos (a r : ℝ) : 0 < bandGeometricRatio a r :=
  mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)

theorem bandGeometricRatio_lt_one {a r : ℝ} (ha : 0 < a) (har : a < r) :
    bandGeometricRatio a r < 1 := by
  have hexp : 1 / r < 1 / a := one_div_lt_one_div_of_lt ha har
  have hpow := Real.rpow_lt_rpow_of_exponent_gt
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hexp
  have hmul := mul_lt_mul_of_pos_left hpow
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (1 / r))
  have hunit : (2 : ℝ) ^ (1 / r) * (1 / 2 : ℝ) ^ (1 / r) = 1 := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  exact hmul.trans_eq hunit

theorem band_length_times_size (a r : ℝ) (k : ℕ) :
    ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 / r) * ((1 / 2 : ℝ) ^ k) ^ (1 / a) =
      (2 : ℝ) ^ (1 / r) * bandGeometricRatio a r ^ k := by
  rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ,
    Real.mul_rpow (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)
      (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  simp only [bandGeometricRatio, mul_pow]
  ring

theorem finite_geometric_sum_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (K : ℕ) :
    (∑ k ∈ Finset.range K, ρ ^ k) ≤ 1 / (1 - ρ) := by
  have hid : (∑ k ∈ Finset.range K, ρ ^ k) * (1 - ρ) = 1 - ρ ^ K := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith
  apply (le_div_iff₀ (sub_pos.mpr hρ1)).mpr
  rw [hid]
  exact sub_le_self _ (pow_nonneg hρ0 K)

theorem finite_band_bound {a r χ : ℝ} (ha : 0 < a) (har : a < r) (hχ : 0 ≤ χ)
    (K : ℕ) :
    (∑ k ∈ Finset.range K,
      χ * ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 / r) * ((1 / 2 : ℝ) ^ k) ^ (1 / a)) ≤
      (χ * (2 : ℝ) ^ (1 / r)) / (1 - bandGeometricRatio a r) := by
  have hterm (k : ℕ) :
      χ * ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 / r) * ((1 / 2 : ℝ) ^ k) ^ (1 / a) =
      (χ * (2 : ℝ) ^ (1 / r)) * bandGeometricRatio a r ^ k := by
    rw [mul_assoc, band_length_times_size, ← mul_assoc]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left
    (finite_geometric_sum_le (bandGeometricRatio_pos a r).le (bandGeometricRatio_lt_one ha har) K)
    (mul_nonneg hχ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 / r)))
  simpa only [mul_one_div] using h

end MarkovSuperreflexivity

end

end OAI
