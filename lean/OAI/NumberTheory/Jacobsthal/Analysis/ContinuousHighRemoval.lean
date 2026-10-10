import OAI.NumberTheory.Jacobsthal.Estimates.LogSquaredDecay
import OAI.NumberTheory.Jacobsthal.Paths.HighPrefixBounds

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.ContinuousHighRemoval

open Filter
open scoped ENNReal Topology
open HighPrefixBounds LogSquaredDecay

lemma tail_coefficient_eq (ell B : ℝ) (m : ℕ) :
    ((2:ℝ≥0∞)⁻¹)^m*ENNReal.ofReal ((B/ell)^2) =
      ENNReal.ofReal ((1/2:ℝ)^m*(B/ell)^2) := by
  have hh : (2:ℝ≥0∞)⁻¹=ENNReal.ofReal (1/2:ℝ) := by
    rw [one_div,ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2)]
    norm_num
  rw [hh,← ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤1/2),
    ← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0:ℝ)≤1/2) m)]

lemma tail_coefficient_bound {ell B : ℝ} (hell : 1≤ell) (hB : ell≤B) :
    ((2:ℝ≥0∞)⁻¹)^⌊(Real.log B)^2/2⌋₊ * ENNReal.ofReal ((B/ell)^2) ≤
      ENNReal.ofReal (2*B^2*Real.exp (-Real.log 2*((Real.log B)^2/2))) := by
  rw [tail_coefficient_eq]
  apply ENNReal.ofReal_le_ofReal
  have hB0 : 0≤B := zero_le_one.trans (hell.trans hB)
  have hell0 : 0<ell := zero_lt_one.trans_le hell
  have hr0 : 0≤B/ell := div_nonneg hB0 hell0.le
  have hr : B/ell≤B := div_le_self hB0 hell
  have hsq : (B/ell)^2≤B^2 := by
    simpa only [pow_two] using mul_le_mul hr hr hr0 hB0
  calc
    _ ≤ (2*Real.exp (-Real.log 2*((Real.log B)^2/2)))*B^2 :=
      mul_le_mul (half_floor_bound ((Real.log B)^2)) hsq (sq_nonneg _) (by positivity)
    _ = _ := by ring

lemma reward_coefficient_bound {ell B c : ℝ} (hell : 1≤ell) (hB : ell≤B) (hc : 0≤c) :
    ENNReal.ofReal (Real.exp (-c*((Real.log B)^2*ell/2))) * ENNReal.ofReal (B/ell) ≤
      ENNReal.ofReal (B*Real.exp (-c*((Real.log B)^2/2))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  have hB0 : 0≤B := zero_le_one.trans (hell.trans hB)
  have hell0 : 0<ell := zero_lt_one.trans_le hell
  have hr0 : 0≤B/ell := div_nonneg hB0 hell0.le
  have hr : B/ell≤B := div_le_self hB0 hell
  have he : Real.exp (-c*((Real.log B)^2*ell/2)) ≤ Real.exp (-c*((Real.log B)^2/2)) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hell (mul_nonneg hc (sq_nonneg (Real.log B)))
    nlinarith
  exact (mul_le_mul he hr hr0 (Real.exp_pos _).le).trans_eq (mul_comm _ _)

lemma tail_saving (A : ℝ) : ∀ᶠ B : ℝ in atTop,
    2*B^2*Real.exp (-Real.log 2*((Real.log B)^2/2)) ≤ (1/2)*B^(-A) := by
  simpa only [Real.rpow_two] using
    constant_power_saving (Real.log_pos (by norm_num : (1:ℝ)<2)) 2 2 A

lemma gap_saving {c : ℝ} (hc : 0<c) (A : ℝ) : ∀ᶠ B : ℝ in atTop,
    B*Real.exp (-c*((Real.log B)^2/2)) ≤ (1/2)*B^(-A) := by
  simpa only [Real.rpow_one,one_mul] using constant_power_saving hc 1 1 A

theorem low_gap_high_removal (K A : ℝ) : ∀ᶠ B : ℝ in atTop,
    ∀ ell : ℝ, 1≤ell → ell≤B → ∀ R : ℝ,
      lowHighMass ell ((Real.log B)^2) B R K ≤ ENNReal.ofReal (B^(-A)) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),tail_saving A,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (2*K+1)))] with B hB1 htail hlog
  intro ell hell hB R
  have hell0 : 0<ell := zero_lt_one.trans_le hell
  have hS : 0≤(Real.log B)^2 := sq_nonneg _
  have hm : (⌊(Real.log B)^2/2⌋₊:ℝ)≤(Real.log B)^2/2 := Nat.floor_le (by positivity)
  have hl1 : 1≤Real.log B := (le_max_left _ _).trans hlog
  have hlK : 2*K+1≤Real.log B := (le_max_right _ _).trans hlog
  have hK : K≤(Real.log B)^2*ell/2 := by
    have hmul := mul_le_mul_of_nonneg_left hell hS
    nlinarith
  calc
    _ ≤ ((2:ℝ≥0∞)⁻¹)^⌊(Real.log B)^2/2⌋₊*ENNReal.ofReal ((B/ell)^2) :=
      low_high_bound hell0 hB _ hm hK
    _ ≤ ENNReal.ofReal (2*B^2*Real.exp (-Real.log 2*((Real.log B)^2/2))) := tail_coefficient_bound hell hB
    _ ≤ ENNReal.ofReal ((1/2)*B^(-A)) := ENNReal.ofReal_le_ofReal htail
    _ ≤ ENNReal.ofReal (B^(-A)) := ENNReal.ofReal_le_ofReal (by
      have hh := Real.rpow_nonneg (show 0≤B by linarith) (-A)
      nlinarith)

theorem rewarded_high_removal (c : ℝ) (hc : 0<c) (A : ℝ) : ∀ᶠ B : ℝ in atTop,
    ∀ ell : ℝ, 1≤ell → ell≤B → ∀ R : ℝ,
      rewardedHighMass ell ((Real.log B)^2) B R c ≤ ENNReal.ofReal (B^(-A)) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),tail_saving A,gap_saving hc A] with B hB1 htail hgap
  intro ell hell hB R
  have hell0 : 0<ell := zero_lt_one.trans_le hell
  have hm : (⌊(Real.log B)^2/2⌋₊:ℝ)≤(Real.log B)^2/2 := Nat.floor_le (by positivity)
  have hT : ((2:ℝ≥0∞)⁻¹)^⌊(Real.log B)^2/2⌋₊*ENNReal.ofReal ((B/ell)^2) ≤
      ENNReal.ofReal ((1/2)*B^(-A)) :=
    (tail_coefficient_bound hell hB).trans (ENNReal.ofReal_le_ofReal htail)
  have hG : ENNReal.ofReal (Real.exp (-c*((Real.log B)^2*ell/2)))*ENNReal.ofReal (B/ell) ≤
      ENNReal.ofReal ((1/2)*B^(-A)) :=
    (reward_coefficient_bound hell hB hc.le).trans (ENNReal.ofReal_le_ofReal hgap)
  have hnonneg : 0≤(1/2)*B^(-A) := mul_nonneg (by norm_num)
    (Real.rpow_nonneg (show 0≤B by linarith) _)
  calc
    _ ≤ ((2:ℝ≥0∞)⁻¹)^⌊(Real.log B)^2/2⌋₊*ENNReal.ofReal ((B/ell)^2) +
        ENNReal.ofReal (Real.exp (-c*((Real.log B)^2*ell/2)))*ENNReal.ofReal (B/ell) :=
      rewarded_high_bound hell0 hB hc.le _ hm
    _ ≤ ENNReal.ofReal ((1/2)*B^(-A)) + ENNReal.ofReal ((1/2)*B^(-A)) := add_le_add hT hG
    _ = ENNReal.ofReal (B^(-A)) := by
      rw [← ENNReal.ofReal_add hnonneg hnonneg]
      congr 1
      ring

end ErdosPrimeInputs.ContinuousHighRemoval

end

end Erdos970

end OAI
