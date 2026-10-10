import OAI.InformationTheory.BooleanNoise.EntropyBounds
import OAI.InformationTheory.BooleanNoise.CurvatureCertificates

namespace OAI

noncomputable section

open Finset Set
open scoped BigOperators

namespace LeanBlast.CourtadeKumar

def curvatureNumeratorCoeff (k : ℕ) : ℝ :=
  1 / (2 * (k : ℝ) + 1) + 1 / (2 * (k : ℝ) + 3)

theorem curvatureNumeratorCoeff_nonneg (k : ℕ) : 0 ≤ curvatureNumeratorCoeff k := by
  unfold curvatureNumeratorCoeff
  positivity

theorem curvatureNumeratorCoeff_antitone : Antitone curvatureNumeratorCoeff := by
  intro i j hij
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  unfold curvatureNumeratorCoeff
  exact add_le_add (one_div_le_one_div_of_le (by positivity) (by linarith))
    (one_div_le_one_div_of_le (by positivity) (by linarith))

theorem hasSum_artanh_div {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasSum (fun k : ℕ => (1 / (2 * (k : ℝ) + 1)) * (u ^ 2) ^ k)
      (Real.artanh u / u) := by
  have h := (hasSum_artanh (show |u| < 1 by rwa [abs_of_pos hu0])).div_const u
  convert h using 1
  ext k
  rw [pow_add, pow_one, ← pow_mul]
  field_simp

theorem hasSum_curvatureNumerator {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasSum (fun k : ℕ => curvatureNumeratorCoeff k * (u ^ 2) ^ k)
      (((1 + u ^ 2) * Real.artanh u - u) / u ^ 3) := by
  have hA := hasSum_artanh_div hu0 hu1
  have htail := (hasSum_nat_add_iff' 1).mpr hA
  have hB : HasSum (fun k : ℕ => (1 / (2 * (k : ℝ) + 3)) * (u ^ 2) ^ k)
      ((Real.artanh u / u - 1) / u ^ 2) := by
    have hdiv := htail.div_const (u ^ 2)
    convert hdiv using 1
    · ext k
      simp only [Nat.cast_add, Nat.cast_one]
      rw [pow_succ]
      field_simp
      ring
    · simp
  convert hA.add hB using 1
  · ext k
    unfold curvatureNumeratorCoeff
    ring
  · field_simp
    ring

theorem curvatureT_lower {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    u * curvatureT (u ^ 2) ≤ Real.artanh u := by
  have h := sum_range_artanh_le hu0.le hu1 6
  convert h using 1
  norm_num [curvatureT, Finset.sum_range_succ]
  ring

theorem curvatureP_upper {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    entropy u ≤ curvatureP (u ^ 2) := by
  have h := sum_range_psi_le (show |u| < 1 by rwa [abs_of_pos hu0]) 5
  have hs : (∑ k ∈ Finset.range 5, psiCoeff k * u ^ (2 * (k + 1))) =
      u ^ 2 / 2 + (u ^ 2) ^ 2 / 12 + (u ^ 2) ^ 3 / 30 +
        (u ^ 2) ^ 4 / 56 + (u ^ 2) ^ 5 / 90 := by
    norm_num [psiCoeff, Finset.sum_range_succ]
    ring
  rw [hs] at h
  unfold entropy curvatureP
  linarith [ell_lt_347_div_500]

theorem curvatureNumerator_upper {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (((1 + u ^ 2) * Real.artanh u - u) / u ^ 3) ≤
      curvatureN (u ^ 2) / (1 - u ^ 2) := by
  have hz0 : 0 ≤ u ^ 2 := sq_nonneg u
  have hz1 : u ^ 2 < 1 := by nlinarith [mul_pos hu0 (sub_pos.mpr hu1)]
  have hz : 1 - u ^ 2 ≠ 0 := by linarith
  have hA := hasSum_curvatureNumerator hu0 hu1
  have htail := (hasSum_nat_add_iff' 5).mpr hA
  have hgeo := (hasSum_geometric_of_lt_one hz0 hz1).mul_left
    (curvatureNumeratorCoeff 5 * (u ^ 2) ^ 5)
  have hbound := hasSum_le
    (fun k : ℕ => calc
      curvatureNumeratorCoeff (k + 5) * (u ^ 2) ^ (k + 5) ≤
          curvatureNumeratorCoeff 5 * (u ^ 2) ^ (k + 5) :=
        mul_le_mul_of_nonneg_right
          (curvatureNumeratorCoeff_antitone (by omega)) (pow_nonneg hz0 _)
      _ = (curvatureNumeratorCoeff 5 * (u ^ 2) ^ 5) * (u ^ 2) ^ k := by
        rw [pow_add]
        ring) htail hgeo
  have hpartial :
      (∑ k ∈ Finset.range 5, curvatureNumeratorCoeff k * (u ^ 2) ^ k) +
          (curvatureNumeratorCoeff 5 * (u ^ 2) ^ 5) * (1 - u ^ 2)⁻¹ =
        curvatureN (u ^ 2) / (1 - u ^ 2) := by
    norm_num [curvatureNumeratorCoeff, Finset.sum_range_succ, curvatureN]
    field_simp
  rw [← hpartial]
  linarith

theorem medium_curvature_bound {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hz : u ^ 2 ≤ (2 / 3 : ℝ)) :
    entropy u ^ 2 * (((1 + u ^ 2) * Real.artanh u - u) /
      ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 3)) ≤ 2 / 3 := by
  have hz0 : 0 ≤ u ^ 2 := sq_nonneg u
  have hz1 : 0 < 1 - u ^ 2 := by linarith
  have ht : 0 < Real.artanh u := Real.artanh_pos ⟨hu0, hu1⟩
  have hH : 0 < entropy u := entropy_pos ⟨by linarith, hu1⟩
  have hHP := curvatureP_upper hu0 hu1
  have hP : 0 < curvatureP (u ^ 2) := hH.trans_le hHP
  have hT : 0 < curvatureT (u ^ 2) := by unfold curvatureT; positivity
  have hTl := curvatureT_lower hu0 hu1
  have hN := curvatureNumerator_upper hu0 hu1
  have hnum : (1 + u ^ 2) * Real.artanh u - u ≤
      (curvatureN (u ^ 2) / (1 - u ^ 2)) * u ^ 3 :=
    (div_le_iff₀ (pow_pos hu0 3)).mp hN
  have hu_atanh : u ≤ Real.artanh u := by
    simpa using sum_range_artanh_le hu0.le hu1 1
  have hnum0 : 0 ≤ (1 + u ^ 2) * Real.artanh u - u := by
    nlinarith [mul_nonneg hz0 ht.le]
  have hsq : entropy u ^ 2 ≤ curvatureP (u ^ 2) ^ 2 :=
    pow_le_pow_left₀ hH.le hHP 2
  have hprod := mul_le_mul hsq hnum hnum0 (sq_nonneg (curvatureP (u ^ 2)))
  have hc := curvatureCertificate_pos hz0 hz
  unfold curvaturePolynomial at hc
  have hc' : 3 * curvatureP (u ^ 2) ^ 2 * curvatureN (u ^ 2) <
      2 * (1 - u ^ 2) ^ 3 * curvatureT (u ^ 2) ^ 3 := by linarith
  have hcert : curvatureP (u ^ 2) ^ 2 *
      ((curvatureN (u ^ 2) / (1 - u ^ 2)) * u ^ 3) <
      (2 / 3 : ℝ) * (1 - u ^ 2) ^ 2 * (u * curvatureT (u ^ 2)) ^ 3 := by
    rw [show curvatureP (u ^ 2) ^ 2 *
        ((curvatureN (u ^ 2) / (1 - u ^ 2)) * u ^ 3) =
        (curvatureP (u ^ 2) ^ 2 * curvatureN (u ^ 2) * u ^ 3) / (1 - u ^ 2) by ring]
    apply (div_lt_iff₀ hz1).mpr
    have hc'' := mul_lt_mul_of_pos_right hc' (pow_pos hu0 3)
    nlinarith
  have hpow : (u * curvatureT (u ^ 2)) ^ 3 ≤ (Real.artanh u) ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg hu0.le hT.le) hTl 3
  have hden := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (2 / 3 : ℝ) * (1 - u ^ 2) ^ 2 by positivity)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (mul_pos (pow_pos hz1 2) (pow_pos ht 3))).mpr
  calc
    entropy u ^ 2 * ((1 + u ^ 2) * Real.artanh u - u) ≤
        curvatureP (u ^ 2) ^ 2 *
          ((curvatureN (u ^ 2) / (1 - u ^ 2)) * u ^ 3) := hprod
    _ ≤ (2 / 3 : ℝ) * (1 - u ^ 2) ^ 2 * (u * curvatureT (u ^ 2)) ^ 3 := hcert.le
    _ ≤ (2 / 3 : ℝ) * ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 3) := by
      simpa only [mul_assoc] using hden

end LeanBlast.CourtadeKumar

end

end OAI
