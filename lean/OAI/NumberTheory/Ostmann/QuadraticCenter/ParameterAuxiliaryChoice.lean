import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterAuxiliaryBand

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

lemma auxiliaryK_le_T {T y : ℝ} {Z z : ℕ} (hT : 0 ≤ T) (hy : 1 ≤ y)
    (hZ0 : 0 ≤ Real.log Z) (hZu : Real.log Z ≤ 2 * T)
    (hz : 1 ≤ z) (hzl : y / 2 ≤ Real.log z) : (auxiliaryK Z z : ℝ) ≤ T := by
  have hzr : (0 : ℝ) < z := by exact_mod_cast hz
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hden : (1 / 2 : ℝ) ≤ Real.log (2 * (z : ℝ)) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hzr.ne']
    linarith
  have hv : 0 ≤ (1 / 50 : ℝ) * Real.log Z / Real.log (2 * (z : ℝ)) :=
    div_nonneg (mul_nonneg (by norm_num) hZ0) (by linarith)
  have hk : (auxiliaryK Z z : ℝ) ≤ (1 / 50 : ℝ) * Real.log Z /
      Real.log (2 * (z : ℝ)) := Nat.floor_le hv
  have hupper : (1 / 50 : ℝ) * Real.log Z / Real.log (2 * (z : ℝ)) ≤ T := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log (2 * (z : ℝ)))).mpr
    nlinarith
  exact hk.trans hupper

lemma eventually_auxiliary_separated :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T / 2 ≤ Real.log Z → Real.log z ≤ 2 * T ^ auxiliaryExponent → 1 ≤ z → 2 * z < Z := by
  filter_upwards [eventually_mul_rpow_le_rpow 16
      (a := auxiliaryExponent) (b := 1) (by norm_num [auxiliaryExponent]),
    eventually_ge_atTop (8 * Real.log 2), eventually_gt_atTop (0 : ℝ)] with T hg hT hpos
  intro Z z hZ hz hz1
  rw [Real.rpow_one] at hg
  have hzr : (0 : ℝ) < z := by exact_mod_cast hz1
  have hlog : Real.log (2 * (z : ℝ)) < Real.log Z := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hzr.ne']
    linarith
  by_contra hn
  have hle : (Z : ℝ) ≤ 2 * (z : ℝ) := by exact_mod_cast (le_of_not_gt hn)
  have hZpos : (0 : ℝ) < Z := by
    by_contra hnZ
    have he : Z = 0 := by exact_mod_cast (le_antisymm (le_of_not_gt hnZ) (Nat.cast_nonneg Z))
    simp only [he, Nat.cast_zero, Real.log_zero] at hZ
    linarith
  exact (not_le_of_gt hlog) (Real.log_le_log hZpos hle)

theorem eventually_actual_auxiliary_product (d : Decomposition) :
    ∀ᶠ T : ℝ in atTop, ∀ Z : ℕ,
      T / 2 ≤ Real.log Z → Real.log Z ≤ 2 * T →
      ∃ (z : ℕ) (F : Finset ℕ),
        1 ≤ z ∧ T ^ auxiliaryExponent / 2 ≤ Real.log z ∧
        Real.log z ≤ 2 * T ^ auxiliaryExponent ∧ 2 * z < Z ∧
        F.card = auxiliaryK Z z ∧ Squarefree (∏ p ∈ F, p) ∧
        (∏ p ∈ F, p) ≤ (2 * z) ^ auxiliaryK Z z ∧
        ((∏ p ∈ F, p) : ℝ) ≤ (Z : ℝ) ^ (1 / 50 : ℝ) ∧
        (∀ p ∈ F, BalancedResiduePrime d p ∧ z ≤ p ∧ p < 2 * z) ∧
        (∀ q : ℕ, Z ≤ q → q ∉ F) := by
  classical
  filter_upwards [eventually_actual_auxiliary_prime_block d, eventually_auxiliary_separated,
    eventually_auxiliary_size_conditions] with T hblock hsep hc
  intro Z hZl hZu
  obtain ⟨j, G, hzl, hzu, hcard, hG⟩ := hblock
  let z := 2 ^ j
  have hz : 1 ≤ z := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero j (by decide : (2 : ℕ) ≠ 0))
  have hT : 0 < T := by linarith [hc.1]
  have hZ0 : 0 ≤ Real.log Z := by linarith
  have hZ : 1 ≤ Z := by
    by_contra hn
    have he : Z = 0 := by omega
    simp only [he, Nat.cast_zero, Real.log_zero] at hZl
    linarith
  have hkT : (auxiliaryK Z z : ℝ) ≤ T :=
    auxiliaryK_le_T hT.le hc.2.1 hZ0 hZu hz hzl
  have hK : auxiliaryK Z z ≤ G.card := by exact_mod_cast hkT.trans hcard
  have hUZ : 2 * z < Z := hsep Z z hZl hzu hz
  obtain ⟨F, hF, hFK, hsq, hprod, hbal, hdisj⟩ :=
    exists_balanced_prime_subproduct d G (fun p hp => (hG p hp).1)
      (auxiliaryK Z z) (2 * z) Z hK (fun p hp => (hG p hp).2.2.1.le) hUZ
  refine ⟨z, F, hz, hzl, hzu, hUZ, hFK, hsq, hprod,
    (by simpa only [Nat.cast_prod] using auxiliary_product_rpow_bound Z z _ hZ hz hprod), ?_, hdisj⟩
  intro p hp
  exact ⟨hbal p hp, (hG p (hF hp)).2.1, (hG p (hF hp)).2.2.1⟩

end Ostmann.QuadraticCenter

end

end OAI
