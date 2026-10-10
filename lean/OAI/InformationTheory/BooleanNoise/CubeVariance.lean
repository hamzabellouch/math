import OAI.InformationTheory.BooleanNoise.CubeSplits
import OAI.InformationTheory.BooleanNoise.JensenGaps
import OAI.InformationTheory.BooleanNoise.PairEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

def binaryRelativeEntropy (a m : ℝ) : ℝ :=
  (1 + a) / 2 * Real.log ((1 + a) / (1 + m)) +
    (1 - a) / 2 * Real.log ((1 - a) / (1 - m))

theorem one_sub_sq_pos_of_interior {a : ℝ} (ha : -1 < a ∧ a < 1) :
    0 < 1 - a ^ 2 := by
  nlinarith [mul_pos (by linarith : 0 < 1 - a) (by linarith : 0 < 1 + a)]

theorem binaryRelativeEntropy_eq {a m : ℝ}
    (ha : -1 < a ∧ a < 1) (hm : -1 < m ∧ m < 1) :
    binaryRelativeEntropy a m = psi a - psi m -
      (a - m) / 2 * (Real.log (1 + m) - Real.log (1 - m)) := by
  have hap : 1 + a ≠ 0 := ne_of_gt (by linarith)
  have ham : 1 - a ≠ 0 := ne_of_gt (by linarith)
  have hmp : 1 + m ≠ 0 := ne_of_gt (by linarith)
  have hmm : 1 - m ≠ 0 := ne_of_gt (by linarith)
  unfold binaryRelativeEntropy psi
  rw [Real.log_div hap hmp, Real.log_div ham hmm]
  ring

theorem sub_le_mul_log_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a - b ≤ a * Real.log (a / b) := by
  have h := mul_le_mul_of_nonneg_left
    (Real.one_sub_inv_le_log_of_pos (div_pos ha hb)) ha.le
  have heq : a * (1 - (a / b)⁻¹) = a - b := by
    field_simp
  rwa [heq] at h

theorem binaryRelativeEntropy_nonneg {a m : ℝ}
    (ha : -1 < a ∧ a < 1) (hm : -1 < m ∧ m < 1) :
    0 ≤ binaryRelativeEntropy a m := by
  have hp := sub_le_mul_log_div (a := 1 + a) (b := 1 + m)
    (by linarith) (by linarith)
  have hm' := sub_le_mul_log_div (a := 1 - a) (b := 1 - m)
    (by linarith) (by linarith)
  unfold binaryRelativeEntropy
  nlinarith

theorem binaryRelativeEntropy_le_sq_div {a m : ℝ}
    (ha : -1 < a ∧ a < 1) (hm : -1 < m ∧ m < 1) :
    binaryRelativeEntropy a m ≤ (a - m) ^ 2 / (1 - m ^ 2) := by
  have hmp : 1 + m ≠ 0 := ne_of_gt (by linarith)
  have hmm : 1 - m ≠ 0 := ne_of_gt (by linarith)
  have hA : 1 - m ^ 2 ≠ 0 := ne_of_gt (one_sub_sq_pos_of_interior hm)
  have hp := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos
      (div_pos (by linarith : 0 < 1 + a) (by linarith : 0 < 1 + m)))
    (show 0 ≤ (1 + a) / 2 by linarith)
  have hn := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos
      (div_pos (by linarith : 0 < 1 - a) (by linarith : 0 < 1 - m)))
    (show 0 ≤ (1 - a) / 2 by linarith)
  calc
    binaryRelativeEntropy a m ≤
        (1 + a) / 2 * ((1 + a) / (1 + m) - 1) +
          (1 - a) / 2 * ((1 - a) / (1 - m) - 1) := add_le_add hp hn
    _ = (a - m) ^ 2 / (1 - m ^ 2) := by
      field_simp
      ring

theorem informationDeficit_eq_average_psi (g : Cube n → ℝ) :
    informationDeficit g = cubeAverage (fun x => psi (g x)) - psi (cubeAverage g) := by
  unfold informationDeficit entropyAverage entropy
  rw [cubeAverage_sub, cubeAverage_const]
  ring

theorem informationDeficit_eq_average_binaryRelativeEntropy
    {g : Cube n → ℝ} (hg : IsInterior g) :
    informationDeficit g =
      cubeAverage (fun x => binaryRelativeEntropy (g x) (cubeAverage g)) := by
  let m := cubeAverage g
  let c := Real.log (1 + m) - Real.log (1 - m)
  have hlin : cubeAverage (fun x => (g x - m) / 2 * c) = 0 := by
    have heq : (fun x => (g x - m) / 2 * c) = (fun x => (c / 2) * (g x - m)) := by
      funext x
      ring
    rw [heq, cubeAverage_smul, cubeAverage_sub, cubeAverage_const]
    dsimp [m]
    ring
  have heq : (fun x => binaryRelativeEntropy (g x) m) =
      (fun x => psi (g x) - psi m - (g x - m) / 2 * c) := by
    funext x
    exact binaryRelativeEntropy_eq (hg x) hg.cubeAverage
  rw [show (fun x => binaryRelativeEntropy (g x) (cubeAverage g)) =
      (fun x => binaryRelativeEntropy (g x) m) from rfl, heq]
  rw [cubeAverage_sub, cubeAverage_sub, cubeAverage_const, hlin, sub_zero]
  exact informationDeficit_eq_average_psi g

theorem informationDeficit_nonneg {g : Cube n → ℝ} (hg : IsInterior g) :
    0 ≤ informationDeficit g := by
  rw [informationDeficit_eq_average_binaryRelativeEntropy hg]
  exact cubeAverage_nonneg fun x => binaryRelativeEntropy_nonneg (hg x) hg.cubeAverage

theorem informationDeficit_le_variance_div {g : Cube n → ℝ} (hg : IsInterior g) :
    informationDeficit g ≤ cubeVariance g / meanVariance g := by
  rw [informationDeficit_eq_average_binaryRelativeEntropy hg]
  calc
    cubeAverage (fun x => binaryRelativeEntropy (g x) (cubeAverage g)) ≤
        cubeAverage (fun x => (g x - cubeAverage g) ^ 2 / (1 - (cubeAverage g) ^ 2)) :=
      cubeAverage_mono fun x => binaryRelativeEntropy_le_sq_div (hg x) hg.cubeAverage
    _ = cubeVariance g / meanVariance g := cubeAverage_div _ _

theorem abs_cubeAverage_le (g : Cube n → ℝ) :
    |cubeAverage g| ≤ cubeAverage (fun x => |g x|) := by
  unfold cubeAverage
  rw [abs_div, abs_of_pos (cube_denominator_pos n)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (cube_denominator_pos n).le

theorem cubeAverage_pairDomain {a b : Cube n → ℝ}
    (hdom : ∀ x, |a x| + |b x| < 1) :
    |cubeAverage a| + |cubeAverage b| < 1 := by
  calc
    |cubeAverage a| + |cubeAverage b| ≤
        cubeAverage (fun x => |a x|) + cubeAverage (fun x => |b x|) :=
      add_le_add (abs_cubeAverage_le a) (abs_cubeAverage_le b)
    _ = cubeAverage (fun x => |a x| + |b x|) := (cubeAverage_add _ _).symm
    _ < 1 := by simpa using cubeAverage_lt hdom

theorem IsInterior.of_pairDomain_left {a b : Cube n → ℝ}
    (hdom : ∀ x, |a x| + |b x| < 1) : IsInterior a := by
  intro x
  apply abs_lt.mp
  exact lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg _)) (hdom x)

theorem average_one_sub_sq_pos {g : Cube n → ℝ} (hg : IsInterior g) :
    0 < cubeAverage (fun x => 1 - (g x) ^ 2) := by
  have h := cubeAverage_lt (fun x => one_sub_sq_pos_of_interior (hg x))
  simpa using h

theorem scaled_informationDeficit_le_variance_gap (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) :
    ((cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2)) * informationDeficit a ≤
      cubeAverage (fun x => (b x) ^ 2 / (1 - (a x) ^ 2)) -
        (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2) := by
  have ha : IsInterior a := IsInterior.of_pairDomain_left hdom
  let A := 1 - (cubeAverage a) ^ 2
  let W := cubeAverage (fun x => 1 - (a x) ^ 2)
  let q := (cubeAverage b) ^ 2 / A
  have hA : 0 < A := one_sub_sq_pos_of_interior ha.cubeAverage
  have hW : 0 < W := average_one_sub_sq_pos ha
  have hvar : 0 ≤ cubeVariance a := cubeVariance_nonneg a
  have hWA : W = A - cubeVariance a := average_one_sub_sq_eq_meanVariance_sub_variance a
  have hWle : W ≤ A := by linarith
  have hq : 0 ≤ q := div_nonneg (sq_nonneg _) hA.le
  have hSa : informationDeficit a ≤ cubeVariance a / W :=
    (informationDeficit_le_variance_div ha).trans
      (div_le_div_of_nonneg_left hvar hW hWle)
  have halg : q * (cubeVariance a / W) = (cubeAverage b) ^ 2 / W -
      (cubeAverage b) ^ 2 / A := by
    have hv : cubeVariance a = A - W := by linarith
    rw [hv]
    dsimp [q]
    field_simp
  calc
    q * informationDeficit a ≤ q * (cubeVariance a / W) :=
      mul_le_mul_of_nonneg_left hSa hq
    _ = (cubeAverage b) ^ 2 / W - (cubeAverage b) ^ 2 / A := halg
    _ ≤ _ := pair_variance_gap_lower_bound a b hdom

theorem entropy_product_le_scaled_informationDeficit (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) :
    pairEntropyGap (cubeAverage a) (cubeAverage b) * informationDeficit a / ell ≤
      ((cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2)) * informationDeficit a := by
  have hSa : 0 ≤ informationDeficit a :=
    informationDeficit_nonneg (IsInterior.of_pairDomain_left hdom)
  have hJ := pairEntropyGap_le_quadratic (cubeAverage a) (cubeAverage b)
    (cubeAverage_pairDomain hdom)
  have hJdiv : pairEntropyGap (cubeAverage a) (cubeAverage b) / ell ≤
      (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2) := by
    apply (div_le_iff₀ ell_pos).2
    exact hJ.trans_eq (mul_comm _ _)
  calc
    pairEntropyGap (cubeAverage a) (cubeAverage b) * informationDeficit a / ell =
        (pairEntropyGap (cubeAverage a) (cubeAverage b) / ell) * informationDeficit a := by
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hJdiv hSa

theorem entropy_product_le_variance_gap (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) :
    pairEntropyGap (cubeAverage a) (cubeAverage b) * informationDeficit a / ell ≤
      cubeAverage (fun x => (b x) ^ 2 / (1 - (a x) ^ 2)) -
        (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2) :=
  (entropy_product_le_scaled_informationDeficit a b hdom).trans
    (scaled_informationDeficit_le_variance_gap a b hdom)

end LeanBlast.CourtadeKumar

end

end OAI
