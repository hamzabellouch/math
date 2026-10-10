import OAI.InformationTheory.BooleanNoise.InverseScalars
import OAI.InformationTheory.BooleanNoise.LambdaScalars
import OAI.InformationTheory.BooleanNoise.PerspectiveJensen
import OAI.InformationTheory.BooleanNoise.EntropyScalars
import OAI.InformationTheory.BooleanNoise.EntropyBounds
import OAI.InformationTheory.BooleanNoise.CubeSplits
import OAI.InformationTheory.BooleanNoise.JensenGaps
import OAI.InformationTheory.BooleanNoise.LShape
import OAI.InformationTheory.BooleanNoise.NormalizedPair
import OAI.InformationTheory.BooleanNoise.PerspectiveInequality
import Mathlib.Tactic

namespace OAI

noncomputable section

open scoped BigOperators
open Set

namespace LeanBlast.CourtadeKumar

theorem IsIncreasing.restrict {n : ℕ} {g : Cube (n + 1) → ℝ}
    (hg : IsIncreasing g) (b : Bool) : IsIncreasing (restrict g b) := by
  intro x y hxy
  apply hg
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · exact hxy j

theorem IsIncreasing.pairHalfDifference_nonneg {n : ℕ} {g : Cube (n + 1) → ℝ}
    (hg : IsIncreasing g) (x : Cube n) : 0 ≤ pairHalfDifference g x := by
  have horder : CourtadeKumar.restrict g false x ≤ CourtadeKumar.restrict g true x := by
    apply hg
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact le_rfl
  exact div_nonneg (sub_nonneg.mpr horder) (by norm_num)

theorem scalar_meanVariance_pos {m : ℝ} (hm : |m| < 1) : 0 < 1 - m ^ 2 := by
  have hsq := (sq_lt_sq₀ (abs_nonneg m) (by norm_num : (0 : ℝ) ≤ 1)).mpr hm
  rw [sq_abs] at hsq
  nlinarith

theorem scalar_meanVariance_le_one (m : ℝ) : 1 - m ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg m]

theorem IsInterior.meanVariance_pos {n : ℕ} {g : Cube n → ℝ}
    (hg : IsInterior g) : 0 < meanVariance g :=
  scalar_meanVariance_pos (abs_lt.mpr hg.cubeAverage)

theorem IsInterior.entropyAverage_pos {n : ℕ} {g : Cube n → ℝ}
    (hg : IsInterior g) : 0 < entropyAverage g := by
  have h := cubeAverage_lt (fun x => entropy_pos (hg x))
  simpa only [cubeAverage_const, entropyAverage] using h

theorem average_one_sub_sq_le_meanVariance {n : ℕ} (a : Cube n → ℝ) :
    cubeAverage (fun x => 1 - (a x) ^ 2) ≤ meanVariance a := by
  rw [average_one_sub_sq_eq_meanVariance_sub_variance]
  linarith [cubeVariance_nonneg a]

theorem monotone_pair_average_geometry {n : ℕ} (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) (hb : ∀ x, 0 ≤ b x) :
    |cubeAverage a| < 1 ∧ 0 ≤ cubeAverage b ∧
      cubeAverage b < 1 - |cubeAverage a| ∧
      0 < cubeAverage (fun x => 1 - (a x) ^ 2) ∧
      cubeAverage (fun x => 1 - (a x) ^ 2) ≤ 1 - (cubeAverage a) ^ 2 ∧
      cubeAverage b ≤ cubeAverage (fun x => 1 - (a x) ^ 2) := by
  have ha : IsInterior a := by
    intro x
    apply abs_lt.mp
    linarith [hdom x, abs_nonneg (b x)]
  have hm : |cubeAverage a| < 1 := abs_lt.mpr ha.cubeAverage
  have hk : 0 ≤ cubeAverage b := cubeAverage_nonneg hb
  have hplus : cubeAverage a + cubeAverage b < 1 := by
    have h := cubeAverage_lt (g := fun x => a x + b x) (h := fun _ => 1) (by
      intro x
      have hd := hdom x
      rw [abs_of_nonneg (hb x)] at hd
      linarith [le_abs_self (a x)])
    simpa only [cubeAverage_add, cubeAverage_const] using h
  have hminus : -cubeAverage a + cubeAverage b < 1 := by
    have h := cubeAverage_lt (g := fun x => -a x + b x) (h := fun _ => 1) (by
      intro x
      have hd := hdom x
      rw [abs_of_nonneg (hb x)] at hd
      linarith [neg_le_abs (a x)])
    simpa only [cubeAverage_add, cubeAverage_neg, cubeAverage_const] using h
  have hkm : cubeAverage b < 1 - |cubeAverage a| := by
    by_cases hm0 : 0 ≤ cubeAverage a
    · rw [abs_of_nonneg hm0]
      linarith
    · rw [abs_of_nonpos (le_of_not_ge hm0)]
      linarith
  have hW : 0 < cubeAverage (fun x => 1 - (a x) ^ 2) := by
    have h := cubeAverage_lt (fun x => scalar_meanVariance_pos (abs_lt.mpr (ha x)))
    simpa only [cubeAverage_const] using h
  have hkW : cubeAverage b ≤ cubeAverage (fun x => 1 - (a x) ^ 2) := by
    apply cubeAverage_mono
    intro x
    have hd := hdom x
    rw [abs_of_nonneg (hb x)] at hd
    have ha1 : |a x| ≤ 1 := (abs_lt.mpr (ha x)).le
    have hasq : |a x| ^ 2 ≤ |a x| := by
      nlinarith [mul_nonneg (abs_nonneg (a x)) (sub_nonneg.mpr ha1)]
    nlinarith [sq_abs (a x)]
  exact ⟨hm, hk, hkm, hW, average_one_sub_sq_le_meanVariance a, hkW⟩

theorem halfDifference_sq_lt_meanVariance {m k : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|) :
    k ^ 2 < 1 - m ^ 2 := by
  have hsq := (sq_lt_sq₀ hk (sub_nonneg.mpr hm.le)).mpr hkm
  have ha : |m| ^ 2 ≤ |m| := by
    nlinarith [mul_nonneg (abs_nonneg m) (sub_nonneg.mpr hm.le)]
  nlinarith [sq_abs m]

theorem monotone_split_parameter_bounds {m k W : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|)
    (hW : 0 < W) (hWA : W ≤ 1 - m ^ 2) (hkW : k ≤ W) :
    0 ≤ k ^ 2 / (1 - m ^ 2) ∧ k ^ 2 / (1 - m ^ 2) < 1 ∧
      0 < W / (1 - m ^ 2) ∧ W / (1 - m ^ 2) ≤ 1 ∧
      k ^ 2 / (1 - m ^ 2) ≤ (W / (1 - m ^ 2)) ^ 2 := by
  have hA := scalar_meanVariance_pos hm
  have hA1 := scalar_meanVariance_le_one m
  refine ⟨div_nonneg (sq_nonneg _) hA.le,
    (div_lt_one hA).mpr (halfDifference_sq_lt_meanVariance hm hk hkm),
    div_pos hW hA, (div_le_one hA).mpr hWA, ?_⟩
  have hk2W2 : k ^ 2 ≤ W ^ 2 := (sq_le_sq₀ hk hW.le).mpr hkW
  have hk2A : k ^ 2 * (1 - m ^ 2) ≤ W ^ 2 := by
    calc
      k ^ 2 * (1 - m ^ 2) ≤ k ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hA1 (sq_nonneg _)
      _ = k ^ 2 := mul_one _
      _ ≤ W ^ 2 := hk2W2
  rw [div_pow]
  apply (div_le_div_iff₀ hA (sq_pos_of_pos hA)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hk2A hA.le]

theorem meanSquare_ratio_le_jensen_ratio {m k : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|) :
    k ^ 2 / (1 - m ^ 2) ≤ k / (1 + |m|) := by
  have hA := scalar_meanVariance_pos hm
  have hden : 0 < 1 + |m| := by positivity
  apply (div_le_div_iff₀ hA hden).mpr
  have hprod := mul_le_mul_of_nonneg_left hkm.le
    (mul_nonneg hk hden.le)
  rw [← sq_abs m]
  nlinarith [hprod]

theorem jensen_ratio_mem_unit_interval {m k : ℝ}
    (hk : 0 ≤ k) (hkm : k < 1 - |m|) :
    0 ≤ k / (1 + |m|) ∧ k / (1 + |m|) < 1 := by
  have hden : 0 < 1 + |m| := by positivity
  refine ⟨div_nonneg hk hden.le, (div_lt_one hden).mpr ?_⟩
  linarith [abs_nonneg m]

theorem normalized_variance_gap_nonneg {q w : ℝ}
    (hq : 0 ≤ q) (hw : 0 < w) (hw1 : w ≤ 1) :
    0 ≤ q * (1 / w - 1) := by
  have hinv : 1 ≤ 1 / w := (le_div_iff₀ hw).mpr (by simpa using hw1)
  exact mul_nonneg hq (sub_nonneg.mpr hinv)

theorem normalized_variance_gap_identity {A W k : ℝ} (hA : A ≠ 0) (hW : W ≠ 0) :
    k ^ 2 / W - k ^ 2 / A = (k ^ 2 / A) * (1 / (W / A) - 1) := by
  field_simp

theorem normalized_jensen_correction_le {m k W V : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|)
    (hW : 0 < W) (hWA : W ≤ 1 - m ^ 2) (hkW : k ≤ W)
    (hV : k ^ 2 / W - k ^ 2 / (1 - m ^ 2) ≤ V) :
    (k ^ 2 / (1 - m ^ 2)) * (1 / (W / (1 - m ^ 2)) - 1) *
        lambda ((k ^ 2 / (1 - m ^ 2)) ^ 2) ≤
      V * lambda ((k / (1 + |m|)) ^ 2) := by
  obtain ⟨hq, hq1, hw, hw1, _⟩ :=
    monotone_split_parameter_bounds hm hk hkm hW hWA hkW
  obtain ⟨hs, hs1⟩ := jensen_ratio_mem_unit_interval hk hkm
  have hq2 : (k ^ 2 / (1 - m ^ 2)) ^ 2 < 1 := by nlinarith
  have hs2 : (k / (1 + |m|)) ^ 2 < 1 := by nlinarith
  have hqs : (k ^ 2 / (1 - m ^ 2)) ^ 2 ≤ (k / (1 + |m|)) ^ 2 :=
    (sq_le_sq₀ hq hs).mpr (meanSquare_ratio_le_jensen_ratio hm hk hkm)
  have hB := normalized_variance_gap_nonneg hq hw hw1
  have hBV : (k ^ 2 / (1 - m ^ 2)) * (1 / (W / (1 - m ^ 2)) - 1) ≤ V := by
    rwa [← normalized_variance_gap_identity (scalar_meanVariance_pos hm).ne' hW.ne']
  have hlambda := monotoneOn_lambda ⟨sq_nonneg _, hq2⟩ ⟨sq_nonneg _, hs2⟩ hqs
  exact mul_le_mul hBV hlambda (lambda_nonneg (sq_nonneg _) hq2) (hB.trans hBV)

theorem scaled_perspective_bound (F : ℝ → ℝ) {A W k h B : ℝ}
    (hA : 0 < A) (hA1 : A ≤ 1) (hW : 0 < W) (hAk : 0 < A - k ^ 2)
    (hB : 0 ≤ B)
    (hperspective : F (h / A) - (1 - k ^ 2 / A) * F ((h / A) / (1 - k ^ 2 / A)) -
      (W / A) * F ((h / A) / (W / A)) ≤ B) :
    A * F (h / A) - (A - k ^ 2) * F (h / (A - k ^ 2)) - W * F (h / W) ≤ B := by
  have harg1 : (h / A) / (1 - k ^ 2 / A) = h / (A - k ^ 2) := by
    have hden : 1 - k ^ 2 / A = (A - k ^ 2) / A := by field_simp
    rw [hden]
    field_simp
  have harg2 : (h / A) / (W / A) = h / W := by field_simp
  rw [harg1, harg2] at hperspective
  have hscaled := mul_le_mul_of_nonneg_left hperspective hA.le
  have hcoef1 : A * (1 - k ^ 2 / A) = A - k ^ 2 := by field_simp
  have hcoef2 : A * (W / A) = W := by field_simp
  have hleft : A * (F (h / A) - (1 - k ^ 2 / A) * F (h / (A - k ^ 2)) -
      (W / A) * F (h / W)) =
      A * F (h / A) - (A - k ^ 2) * F (h / (A - k ^ 2)) - W * F (h / W) := by
    rw [mul_sub, mul_sub, ← mul_assoc, hcoef1, ← mul_assoc, hcoef2]
  rw [hleft] at hscaled
  exact hscaled.trans (by nlinarith)

theorem monotone_dissipation_step_algebra (F : ℝ → ℝ)
    {S Jm A k h W B Drestr Dpair : ℝ}
    (hrestr : 2 * (S - Jm) + (A - k ^ 2) * F (h / (A - k ^ 2)) ≤ Drestr)
    (hpair : W * F (h / W) + B ≤ Dpair - 2 * Jm)
    (hperspective : A * F (h / A) - (A - k ^ 2) * F (h / (A - k ^ 2)) -
      W * F (h / W) ≤ B) :
    2 * S + A * F (h / A) ≤ Drestr + Dpair := by
  linarith

theorem monotone_pair_correction {m k W h Je Jm V Dpair : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|)
    (hW : 0 < W) (hWA : W ≤ 1 - m ^ 2) (hkW : k ≤ W)
    (hV : k ^ 2 / W - k ^ 2 / (1 - m ^ 2) ≤ V)
    (hnormalized : W * L (h / W) ≤ Dpair - 2 * Je)
    (hgap : V * lambda ((k / (1 + |m|)) ^ 2) ≤ 2 * (Je - Jm)) :
    W * L (h / W) +
        (k ^ 2 / (1 - m ^ 2)) * (1 / (W / (1 - m ^ 2)) - 1) *
          lambda ((k ^ 2 / (1 - m ^ 2)) ^ 2) ≤ Dpair - 2 * Jm := by
  have hcorrection := normalized_jensen_correction_le hm hk hkm hW hWA hkW hV
  linarith

theorem monotone_dissipation_step_of_perspective
    {m k W h S Je Jm V Drestr Dpair : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|)
    (hW : 0 < W) (hWA : W ≤ 1 - m ^ 2) (hkW : k ≤ W)
    (hV : k ^ 2 / W - k ^ 2 / (1 - m ^ 2) ≤ V)
    (hrestr : 2 * (S - Jm) + (1 - m ^ 2 - k ^ 2) *
      L (h / (1 - m ^ 2 - k ^ 2)) ≤ Drestr)
    (hnormalized : W * L (h / W) ≤ Dpair - 2 * Je)
    (hgap : V * lambda ((k / (1 + |m|)) ^ 2) ≤ 2 * (Je - Jm))
    (hperspective : L (h / (1 - m ^ 2)) -
      (1 - k ^ 2 / (1 - m ^ 2)) *
        L ((h / (1 - m ^ 2)) / (1 - k ^ 2 / (1 - m ^ 2))) -
      (W / (1 - m ^ 2)) * L ((h / (1 - m ^ 2)) / (W / (1 - m ^ 2))) ≤
      (k ^ 2 / (1 - m ^ 2)) * (1 / (W / (1 - m ^ 2)) - 1) *
        lambda ((k ^ 2 / (1 - m ^ 2)) ^ 2)) :
    2 * S + (1 - m ^ 2) * L (h / (1 - m ^ 2)) ≤ Drestr + Dpair := by
  have hA := scalar_meanVariance_pos hm
  have hAk : 0 < 1 - m ^ 2 - k ^ 2 := by
    linarith [halfDifference_sq_lt_meanVariance hm hk hkm]
  obtain ⟨hq, hq1, hw, hw1, _⟩ :=
    monotone_split_parameter_bounds hm hk hkm hW hWA hkW
  have hq2 : (k ^ 2 / (1 - m ^ 2)) ^ 2 < 1 := by nlinarith
  have hB := mul_nonneg (normalized_variance_gap_nonneg hq hw hw1)
    (lambda_nonneg (sq_nonneg _) hq2)
  have hp := scaled_perspective_bound L hA (scalar_meanVariance_le_one m) hW hAk hB
    hperspective
  have hc := monotone_pair_correction hm hk hkm hW hWA hkW hV hnormalized hgap
  exact monotone_dissipation_step_algebra L hrestr hc hp

theorem two_point_perspective_jensen (F : ℝ → ℝ)
    (hF : ConvexOn ℝ (Ioi 0) F) {A₀ A₁ H₀ H₁ : ℝ}
    (hA₀ : 0 < A₀) (hA₁ : 0 < A₁) (hH₀ : 0 < H₀) (hH₁ : 0 < H₁) :
    ((A₁ + A₀) / 2) * F (((H₁ + H₀) / 2) / ((A₁ + A₀) / 2)) ≤
      (A₁ * F (H₁ / A₁) + A₀ * F (H₀ / A₀)) / 2 := by
  have hsum : 0 < A₁ + A₀ := add_pos hA₁ hA₀
  have hweights : A₁ / (A₁ + A₀) + A₀ / (A₁ + A₀) = 1 := by field_simp
  have hJ := hF.2 (show H₁ / A₁ ∈ Ioi 0 from div_pos hH₁ hA₁)
    (show H₀ / A₀ ∈ Ioi 0 from div_pos hH₀ hA₀)
    (div_nonneg hA₁.le hsum.le) (div_nonneg hA₀.le hsum.le) hweights
  simp only [smul_eq_mul] at hJ
  have harg : A₁ / (A₁ + A₀) * (H₁ / A₁) +
      A₀ / (A₁ + A₀) * (H₀ / A₀) = (H₁ + H₀) / (A₁ + A₀) := by
    field_simp
  rw [harg] at hJ
  have hhalf : ((H₁ + H₀) / 2) / ((A₁ + A₀) / 2) =
      (H₁ + H₀) / (A₁ + A₀) := by field_simp
  rw [hhalf]
  have hscaled := mul_le_mul_of_nonneg_left hJ (show 0 ≤ (A₁ + A₀) / 2 by positivity)
  have hright : (A₁ + A₀) / 2 *
      (A₁ / (A₁ + A₀) * F (H₁ / A₁) + A₀ / (A₁ + A₀) * F (H₀ / A₀)) =
      (A₁ * F (H₁ / A₁) + A₀ * F (H₀ / A₀)) / 2 := by
    field_simp
  rwa [hright] at hscaled

theorem monotone_dissipation_zero (g : Cube 0 → ℝ) (hg : IsInterior g) :
    2 * informationDeficit g +
      meanVariance g * L (entropyAverage g / meanVariance g) ≤ dissipation g := by
  have hA : 0 < meanVariance g := hg.meanVariance_pos
  have hscalar := ell_mul_one_sub_sq_le_entropy
    (abs_lt.mpr (hg (fun _ => false))).le
  have hratio : ell ≤ entropyAverage g / meanVariance g := by
    apply (le_div_iff₀ hA).mpr
    simpa only [entropyAverage, meanVariance, cubeAverage_zeroDim] using hscalar
  rw [informationDeficit_dim_zero, dissipation_dim_zero, L_eq_zero_of_ell_le hratio]
  simp

theorem averaged_normalized_pair_of_pointwise
    (hconvex : ConvexOn ℝ (Ioi 0) L)
    (hpair : ∀ a b : ℝ, |a| + |b| < 1 →
      (1 - a ^ 2) * L (((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2)) ≤
        pairDissipation a b - 2 * pairEntropyGap a b)
    {n : ℕ} (g : Cube (n + 1) → ℝ) (hg : IsInterior g) :
    cubeAverage (fun x => 1 - (pairMean g x) ^ 2) *
        L (entropyAverage g / cubeAverage (fun x => 1 - (pairMean g x) ^ 2)) ≤
      cubeAverage (fun x => pairDissipation (pairMean g x) (pairHalfDifference g x)) -
        2 * cubeAverage (fun x => pairEntropyGap (pairMean g x) (pairHalfDifference g x)) := by
  let A : Cube n → ℝ := fun x => 1 - (pairMean g x) ^ 2
  let H : Cube n → ℝ := fun x =>
    (entropy (pairMean g x + pairHalfDifference g x) +
      entropy (pairMean g x - pairHalfDifference g x)) / 2
  have hA : ∀ x, 0 < A x := fun x =>
    scalar_meanVariance_pos (abs_lt.mpr (hg.pairMean x))
  have hH : ∀ x, 0 < H x := by
    intro x
    dsimp [H]
    rw [pairMean_add_halfDifference, pairMean_sub_halfDifference]
    exact div_pos (add_pos (entropy_pos (hg.restrict true x))
      (entropy_pos (hg.restrict false x))) (by norm_num)
  have hHavg : cubeAverage H = entropyAverage g := by
    dsimp [H]
    simp only [pairMean_add_halfDifference, pairMean_sub_halfDifference]
    rw [cubeAverage_half_sum]
    exact (entropyAverage_split g).symm
  have hJ := cubeAverage_perspective_jensen L hconvex A H hA hH
  rw [hHavg] at hJ
  have hpoint := cubeAverage_mono (fun x => hpair _ _ (hg.pairDomain x))
  have hcombined := hJ.trans hpoint
  simpa only [A, cubeAverage_sub, cubeAverage_smul] using hcombined

theorem restricted_monotone_dissipation_lower
    (hconvex : ConvexOn ℝ (Ioi 0) L)
    {n : ℕ} (g : Cube (n + 1) → ℝ) (hg : IsInterior g)
    (htrue : 2 * informationDeficit (restrict g true) +
      meanVariance (restrict g true) *
        L (entropyAverage (restrict g true) / meanVariance (restrict g true)) ≤
      dissipation (restrict g true))
    (hfalse : 2 * informationDeficit (restrict g false) +
      meanVariance (restrict g false) *
        L (entropyAverage (restrict g false) / meanVariance (restrict g false)) ≤
      dissipation (restrict g false)) :
    2 * (informationDeficit g - pairEntropyGap (cubeAverage (pairMean g))
        (cubeAverage (pairHalfDifference g))) +
      (meanVariance g - (cubeAverage (pairHalfDifference g)) ^ 2) *
        L (entropyAverage g / (meanVariance g - (cubeAverage (pairHalfDifference g)) ^ 2)) ≤
      (dissipation (restrict g true) + dissipation (restrict g false)) / 2 := by
  have hJ := two_point_perspective_jensen L hconvex
    (hg.restrict false).meanVariance_pos (hg.restrict true).meanVariance_pos
    (hg.restrict false).entropyAverage_pos (hg.restrict true).entropyAverage_pos
  rw [meanVariance_split, ← entropyAverage_split g] at hJ
  have hS := informationDeficit_split g
  linarith

theorem monotone_dissipation_from_scalar_lemmas
    (hconvex : ConvexOn ℝ (Ioi 0) L)
    (hpair : ∀ a b : ℝ, |a| + |b| < 1 →
      (1 - a ^ 2) * L (((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2)) ≤
        pairDissipation a b - 2 * pairEntropyGap a b)
    (hperspective : ∀ x w q : ℝ, 0 < x → 0 < w → w ≤ 1 → 0 ≤ q → q < 1 → q ≤ w ^ 2 →
      L x - (1 - q) * L (x / (1 - q)) - w * L (x / w) ≤
        q * (1 / w - 1) * lambda (q ^ 2)) :
    ∀ {n : ℕ} (g : Cube n → ℝ), IsInterior g → IsIncreasing g →
      2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
        dissipation g := by
  intro n
  induction n with
  | zero =>
      intro g hg _
      exact monotone_dissipation_zero g hg
  | succ n ih =>
      intro g hg hmono
      let a := pairMean g
      let b := pairHalfDifference g
      have hdom : ∀ x, |a x| + |b x| < 1 := hg.pairDomain
      have hb : ∀ x, 0 ≤ b x := hmono.pairHalfDifference_nonneg
      obtain ⟨hm, hk, hkm, hW, hWA, hkW⟩ := monotone_pair_average_geometry a b hdom hb
      have htrue := ih (restrict g true) (hg.restrict true) (hmono.restrict true)
      have hfalse := ih (restrict g false) (hg.restrict false) (hmono.restrict false)
      have hrestr := restricted_monotone_dissipation_lower hconvex g hg htrue hfalse
      have hrestr' :
          2 * (informationDeficit g - pairEntropyGap (cubeAverage a) (cubeAverage b)) +
          (1 - (cubeAverage a) ^ 2 - (cubeAverage b) ^ 2) *
            L (entropyAverage g / (1 - (cubeAverage a) ^ 2 - (cubeAverage b) ^ 2)) ≤
          (dissipation (restrict g true) + dissipation (restrict g false)) / 2 := by
        simpa only [a, b, meanVariance, cubeAverage_pairMean] using hrestr
      have hnorm := averaged_normalized_pair_of_pointwise hconvex hpair g hg
      have hgap := pair_jensen_gap_strengthened a b hdom hb
      have hV := pair_variance_gap_lower_bound a b hdom
      obtain ⟨hq, hq1, hw, hw1, hqw⟩ :=
        monotone_split_parameter_bounds hm hk hkm hW hWA hkW
      have hx : 0 < entropyAverage g / (1 - (cubeAverage a) ^ 2) :=
        div_pos hg.entropyAverage_pos (scalar_meanVariance_pos hm)
      have hp := hperspective _ _ _ hx hw hw1 hq hq1 hqw
      have hfinal := monotone_dissipation_step_of_perspective hm hk hkm hW hWA hkW
        hV hrestr' hnorm hgap hp
      rw [dissipation_split g]
      simpa only [a, b, meanVariance, cubeAverage_pairMean] using hfinal

theorem monotone_dissipation {n : ℕ} (g : Cube n → ℝ)
    (hg : IsInterior g) (hmono : IsIncreasing g) :
    2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
      dissipation g := by
  exact monotone_dissipation_from_scalar_lemmas convexOn_L
    (fun _ _ hab => normalized_pair_bound hab) perspective_inequality g hg hmono

end LeanBlast.CourtadeKumar

end

end OAI
