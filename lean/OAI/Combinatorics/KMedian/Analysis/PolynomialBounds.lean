import Mathlib
import OAI.Combinatorics.KMedian.Analysis.CertificatePolynomials

namespace OAI

section
section
namespace MetricKMedian.Certificates
private theorem p_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1651507 / 6250000) ≤ p X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ p X - (1651507 / 6250000) := by
    calc
      0 ≤ (8026757 / 50000000) * (X - 0) ^ 1 * (1 - X) ^ 3 +
      (53912437 / 100000000) * (X - 0) ^ 2 * (1 - X) ^ 2 +
      (60978037 / 100000000) * (X - 0) ^ 3 * (1 - X) ^ 1 +
      (1473493 / 6250000) * (X - 0) ^ 4 * (1 - X) ^ 0 := by positivity
      _ = p X - (1651507 / 6250000) := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem p_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1651507 / 6250000) ≤ p X := by
  exact p_lower_part0 ha hb

private theorem p_upper_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 1/2 - p X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ 1/2 - p X - 0 := by
    calc
      0 ≤ (1473493 / 6250000) * (X - 0) ^ 0 * (1 - X) ^ 4 +
      (39125019 / 50000000) * (X - 0) ^ 1 * (1 - X) ^ 3 +
      (87542891 / 100000000) * (X - 0) ^ 2 * (1 - X) ^ 2 +
      (6665103 / 20000000) * (X - 0) ^ 3 * (1 - X) ^ 1 := by positivity
      _ = 1/2 - p X - 0 := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem p_upper {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 1/2 - p X := by
  exact p_upper_part0 ha hb

private theorem v_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    1 ≤ v X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ v X - 1 := by
    calc
      0 ≤ (4598493 / 6250000) * (X - 0) ^ 0 * (1 - X) ^ 4 +
      (241471283 / 100000000) * (X - 0) ^ 1 * (1 - X) ^ 3 +
      (66691857 / 25000000) * (X - 0) ^ 2 * (1 - X) ^ 2 +
      (99981621 / 100000000) * (X - 0) ^ 3 * (1 - X) ^ 1 := by positivity
      _ = v X - 1 := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem v_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    1 ≤ v X := by
  exact v_lower_part0 ha hb

private theorem v_upper_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 217/125 - v X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ 217/125 - v X - 0 := by
    calc
      0 ≤ (1507 / 6250000) * (X - 0) ^ 0 * (1 - X) ^ 4 +
      (52928717 / 100000000) * (X - 0) ^ 1 * (1 - X) ^ 3 +
      (43708143 / 25000000) * (X - 0) ^ 2 * (1 - X) ^ 2 +
      (194418379 / 100000000) * (X - 0) ^ 3 * (1 - X) ^ 1 +
      (92 / 125) * (X - 0) ^ 4 * (1 - X) ^ 0 := by positivity
      _ = 217/125 - v X - 0 := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem v_upper {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 217/125 - v X := by
  exact v_upper_part0 ha hb

private theorem k_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (767 / 10000) ≤ k X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ k X - (767 / 10000) := by
    calc
      0 ≤ (141 / 2500) * (X - 0) ^ 1 * (1 - X) ^ 2 +
      (127 / 1000) * (X - 0) ^ 2 * (1 - X) ^ 1 +
      (119 / 1250) * (X - 0) ^ 3 * (1 - X) ^ 0 := by positivity
      _ = k X - (767 / 10000) := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem k_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (767 / 10000) ≤ k X := by
  exact k_lower_part0 ha hb

private theorem k_upper_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 1719/10000-k X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ 1719/10000-k X - 0 := by
    calc
      0 ≤ (119 / 1250) * (X - 0) ^ 0 * (1 - X) ^ 3 +
      (573 / 2500) * (X - 0) ^ 1 * (1 - X) ^ 2 +
      (793 / 5000) * (X - 0) ^ 2 * (1 - X) ^ 1 := by positivity
      _ = 1719/10000-k X - 0 := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem k_upper {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 1719/10000-k X := by
  exact k_upper_part0 ha hb

private theorem h_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (7 / 500) ≤ h X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ h X - (7 / 500) := by
    calc
      0 ≤ (19 / 50) * (X - 0) ^ 0 * (1 - X) ^ 3 +
      (57 / 50) * (X - 0) ^ 1 * (1 - X) ^ 2 +
      (18 / 25) * (X - 0) ^ 2 * (1 - X) ^ 1 := by positivity
      _ = h X - (7 / 500) := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem h_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (7 / 500) ≤ h X := by
  exact h_lower_part0 ha hb

private theorem h_upper_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 197/500-h X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ 197/500-h X - 0 := by
    calc
      0 ≤ (21 / 50) * (X - 0) ^ 2 * (1 - X) ^ 1 +
      (19 / 50) * (X - 0) ^ 3 * (1 - X) ^ 0 := by positivity
      _ = 197/500-h X - 0 := by
        dsimp only [p, v, k, h]
        norm_num
        ring
  linarith only [hcert]

theorem h_upper {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    0 ≤ 197/500-h X := by
  exact h_upper_part0 ha hb


end MetricKMedian.Certificates
end
end

end OAI
