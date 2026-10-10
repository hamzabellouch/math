import Mathlib.Tactic

namespace OAI

/-!
# The potential polynomial certificate

The five quotient polynomials and their quarter-interval Bernstein certificates
are those of Section 7, Lemma "The polynomial F" of the manuscript.
The polynomial identities and inequalities hold over the real numbers.
-/

namespace PositiveEinsteinFour.Potential

noncomputable section

def q0 (n : ℝ) : ℝ :=
  (17837 / 80) * n ^ 4 + (-50531 / 80) * n ^ 3 + (74179 / 80) * n ^ 2 + (-27869 / 80) * n + (641 / 15)

def q1 (n : ℝ) : ℝ :=
  (5687 / 40) * n ^ 6 + (47787 / 40) * n ^ 5 + (-60009 / 20) * n ^ 4 + (15206 / 5) * n ^ 3 + (-173651 / 120) * n ^ 2 + (28609 / 120) * n + (2641 / 60)

def q2 (n : ℝ) : ℝ :=
  (854819 / 240) * n ^ 7 + (-2708953 / 240) * n ^ 6 + (3899477 / 240) * n ^ 5 + (-197057 / 16) * n ^ 4 + (434263 / 90) * n ^ 3 + (-19423 / 20) * n ^ 2 + (2288 / 15) * n + (37 / 180)

def q3 (n : ℝ) : ℝ :=
  (431467 / 40) * n ^ 7 + (-198338 / 5) * n ^ 6 + (620453 / 10) * n ^ 5 + (-2004441 / 40) * n ^ 4 + (2521913 / 120) * n ^ 3 + (-84801 / 20) * n ^ 2 + (1906 / 5) * n + (299 / 120)

def q4 (n : ℝ) : ℝ :=
  (354025 / 16) * n ^ 7 + (-1369095 / 16) * n ^ 6 + (11028947 / 80) * n ^ 5 + (-1827129 / 16) * n ^ 4 + (247214 / 5) * n ^ 3 + (-154144 / 15) * n ^ 2 + (12268 / 15) * n + (62 / 15)

private theorem q0_quarter0 {n : ℝ}
    (hlo : (0 : ℝ) / 4 ≤ n) (hhi : n ≤ (1 : ℝ) / 4) : 0 ≤ q0 n := by
  have hz : 0 ≤ (4 * n - 0) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 0) := by linarith
  have hcert : 61440 * q0 n =
      2625536 * (1 - (4 * n - 0)) ^ 4 +
      5151296 * (4 * n - 0) * (1 - (4 * n - 0)) ^ 3 +
      3261264 * (4 * n - 0) ^ 2 * (1 - (4 * n - 0)) ^ 2 +
      964412 * (4 * n - 0) ^ 3 * (1 - (4 * n - 0)) +
      282419 * (4 * n - 0) ^ 4 := by
    unfold q0
    ring
  have hnonneg : 0 ≤ 61440 * q0 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q0_quarter1 {n : ℝ}
    (hlo : (1 : ℝ) / 4 ≤ n) (hhi : n ≤ (2 : ℝ) / 4) : 0 ≤ q0 n := by
  have hz : 0 ≤ (4 * n - 1) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 1) := by linarith
  have hcert : 61440 * q0 n =
      282419 * (1 - (4 * n - 1)) ^ 4 +
      1294940 * (4 * n - 1) * (1 - (4 * n - 1)) ^ 3 +
      4252848 * (4 * n - 1) ^ 2 * (1 - (4 * n - 1)) ^ 2 +
      5358224 * (4 * n - 1) ^ 3 * (1 - (4 * n - 1)) +
      2171408 * (4 * n - 1) ^ 4 := by
    unfold q0
    ring
  have hnonneg : 0 ≤ 61440 * q0 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q0_quarter2 {n : ℝ}
    (hlo : (2 : ℝ) / 4 ≤ n) (hhi : n ≤ (3 : ℝ) / 4) : 0 ≤ q0 n := by
  have hz : 0 ≤ (4 * n - 2) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 2) := by linarith
  have hcert : 61440 * q0 n =
      2171408 * (1 - (4 * n - 2)) ^ 4 +
      12013040 * (4 * n - 2) * (1 - (4 * n - 2)) ^ 3 +
      24217296 * (4 * n - 2) ^ 2 * (1 - (4 * n - 2)) ^ 2 +
      20902820 * (4 * n - 2) ^ 3 * (1 - (4 * n - 2)) +
      6580667 * (4 * n - 2) ^ 4 := by
    unfold q0
    ring
  have hnonneg : 0 ≤ 61440 * q0 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q0_quarter3 {n : ℝ}
    (hlo : (3 : ℝ) / 4 ≤ n) (hhi : n ≤ (4 : ℝ) / 4) : 0 ≤ q0 n := by
  have hz : 0 ≤ (4 * n - 3) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 3) := by linarith
  have hcert : 61440 * q0 n =
      6580667 * (1 - (4 * n - 3)) ^ 4 +
      31742516 * (4 * n - 3) * (1 - (4 * n - 3)) ^ 3 +
      56736384 * (4 * n - 3) ^ 2 * (1 - (4 * n - 3)) ^ 2 +
      44603648 * (4 * n - 3) ^ 3 * (1 - (4 * n - 3)) +
      13082624 * (4 * n - 3) ^ 4 := by
    unfold q0
    ring
  have hnonneg : 0 ≤ 61440 * q0 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

theorem q0_nonneg {n : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1) : 0 ≤ q0 n := by
  rcases le_total n (1 / 4) with h | h
  · exact q0_quarter0 (by simpa using hn0) h
  rcases le_total n (2 / 4) with h2 | h2
  · exact q0_quarter1 h h2
  rcases le_total n (3 / 4) with h3 | h3
  · exact q0_quarter2 h2 h3
  · exact q0_quarter3 h3 (by simpa using hn1)

private theorem q1_quarter0 {n : ℝ}
    (hlo : (0 : ℝ) / 4 ≤ n) (hhi : n ≤ (1 : ℝ) / 4) : 0 ≤ q1 n := by
  have hz : 0 ≤ (4 * n - 0) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 0) := by linarith
  have hcert : 491520 * q1 n =
      21635072 * (1 - (4 * n - 0)) ^ 6 +
      159106048 * (4 * n - 0) * (1 - (4 * n - 0)) ^ 5 +
      426549504 * (4 * n - 0) ^ 2 * (1 - (4 * n - 0)) ^ 4 +
      571195392 * (4 * n - 0) ^ 3 * (1 - (4 * n - 0)) ^ 3 +
      415062688 * (4 * n - 0) ^ 4 * (1 - (4 * n - 0)) ^ 2 +
      157590852 * (4 * n - 0) ^ 5 * (1 - (4 * n - 0)) +
      24662089 * (4 * n - 0) ^ 6 := by
    unfold q1
    ring
  have hnonneg : 0 ≤ 491520 * q1 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q1_quarter1 {n : ℝ}
    (hlo : (1 : ℝ) / 4 ≤ n) (hhi : n ≤ (2 : ℝ) / 4) : 0 ≤ q1 n := by
  have hz : 0 ≤ (4 * n - 1) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 1) := by linarith
  have hcert : 491520 * q1 n =
      24662089 * (1 - (4 * n - 1)) ^ 6 +
      138354216 * (4 * n - 1) * (1 - (4 * n - 1)) ^ 5 +
      318879508 * (4 * n - 1) ^ 2 * (1 - (4 * n - 1)) ^ 4 +
      391606272 * (4 * n - 1) ^ 3 * (1 - (4 * n - 1)) ^ 3 +
      272514864 * (4 * n - 1) ^ 4 * (1 - (4 * n - 1)) ^ 2 +
      102606208 * (4 * n - 1) ^ 5 * (1 - (4 * n - 1)) +
      16527296 * (4 * n - 1) ^ 6 := by
    unfold q1
    ring
  have hnonneg : 0 ≤ 491520 * q1 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q1_quarter2 {n : ℝ}
    (hlo : (2 : ℝ) / 4 ≤ n) (hhi : n ≤ (3 : ℝ) / 4) : 0 ≤ q1 n := by
  have hz : 0 ≤ (4 * n - 2) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 2) := by linarith
  have hcert : 491520 * q1 n =
      16527296 * (1 - (4 * n - 2)) ^ 6 +
      95721344 * (4 * n - 2) * (1 - (4 * n - 2)) ^ 5 +
      238090544 * (4 * n - 2) ^ 2 * (1 - (4 * n - 2)) ^ 4 +
      328631680 * (4 * n - 2) ^ 3 * (1 - (4 * n - 2)) ^ 3 +
      267653012 * (4 * n - 2) ^ 4 * (1 - (4 * n - 2)) ^ 2 +
      123108392 * (4 * n - 2) ^ 5 * (1 - (4 * n - 2)) +
      25207625 * (4 * n - 2) ^ 6 := by
    unfold q1
    ring
  have hnonneg : 0 ≤ 491520 * q1 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q1_quarter3 {n : ℝ}
    (hlo : (3 : ℝ) / 4 ≤ n) (hhi : n ≤ (4 : ℝ) / 4) : 0 ≤ q1 n := by
  have hz : 0 ≤ (4 * n - 3) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 3) := by linarith
  have hcert : 491520 * q1 n =
      25207625 * (1 - (4 * n - 3)) ^ 6 +
      179383108 * (4 * n - 3) * (1 - (4 * n - 3)) ^ 5 +
      549026592 * (4 * n - 3) ^ 2 * (1 - (4 * n - 3)) ^ 4 +
      921476736 * (4 * n - 3) ^ 3 * (1 - (4 * n - 3)) ^ 3 +
      891131392 * (4 * n - 3) ^ 4 * (1 - (4 * n - 3)) ^ 2 +
      469149696 * (4 * n - 3) ^ 5 * (1 - (4 * n - 3)) +
      104660992 * (4 * n - 3) ^ 6 := by
    unfold q1
    ring
  have hnonneg : 0 ≤ 491520 * q1 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

theorem q1_nonneg {n : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1) : 0 ≤ q1 n := by
  rcases le_total n (1 / 4) with h | h
  · exact q1_quarter0 (by simpa using hn0) h
  rcases le_total n (2 / 4) with h2 | h2
  · exact q1_quarter1 h h2
  rcases le_total n (3 / 4) with h3 | h3
  · exact q1_quarter2 h2 h3
  · exact q1_quarter3 h3 (by simpa using hn1)

private theorem q2_quarter0 {n : ℝ}
    (hlo : (0 : ℝ) / 4 ≤ n) (hhi : n ≤ (1 : ℝ) / 4) : 0 ≤ q2 n := by
  have hz : 0 ≤ (4 * n - 0) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 0) := by linarith
  have hcert : 11796480 * q2 n =
      2424832 * (1 - (4 * n - 0)) ^ 7 +
      466812928 * (4 * n - 0) * (1 - (4 * n - 0)) ^ 6 +
      2033946624 * (4 * n - 0) ^ 2 * (1 - (4 * n - 0)) ^ 5 +
      4141778944 * (4 * n - 0) ^ 3 * (1 - (4 * n - 0)) ^ 4 +
      4911514816 * (4 * n - 0) ^ 4 * (1 - (4 * n - 0)) ^ 3 +
      3459239472 * (4 * n - 0) ^ 5 * (1 - (4 * n - 0)) ^ 2 +
      1332713460 * (4 * n - 0) ^ 6 * (1 - (4 * n - 0)) +
      215332845 * (4 * n - 0) ^ 7 := by
    unfold q2
    ring
  have hnonneg : 0 ≤ 11796480 * q2 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q2_quarter1 {n : ℝ}
    (hlo : (1 : ℝ) / 4 ≤ n) (hhi : n ≤ (2 : ℝ) / 4) : 0 ≤ q2 n := by
  have hz : 0 ≤ (4 * n - 1) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 1) := by linarith
  have hcert : 11796480 * q2 n =
      215332845 * (1 - (4 * n - 1)) ^ 7 +
      1681946370 * (4 * n - 1) * (1 - (4 * n - 1)) ^ 6 +
      5554636932 * (4 * n - 1) ^ 2 * (1 - (4 * n - 1)) ^ 5 +
      10011268904 * (4 * n - 1) ^ 3 * (1 - (4 * n - 1)) ^ 4 +
      10571478896 * (4 * n - 1) ^ 4 * (1 - (4 * n - 1)) ^ 3 +
      6531970656 * (4 * n - 1) ^ 5 * (1 - (4 * n - 1)) ^ 2 +
      2191187648 * (4 * n - 1) ^ 6 * (1 - (4 * n - 1)) +
      310014848 * (4 * n - 1) ^ 7 := by
    unfold q2
    ring
  have hnonneg : 0 ≤ 11796480 * q2 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q2_quarter2 {n : ℝ}
    (hlo : (2 : ℝ) / 4 ≤ n) (hhi : n ≤ (3 : ℝ) / 4) : 0 ≤ q2 n := by
  have hz : 0 ≤ (4 * n - 2) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 2) := by linarith
  have hcert : 11796480 * q2 n =
      310014848 * (1 - (4 * n - 2)) ^ 7 +
      2149020224 * (4 * n - 2) * (1 - (4 * n - 2)) ^ 6 +
      6278966112 * (4 * n - 2) ^ 2 * (1 - (4 * n - 2)) ^ 5 +
      10081126224 * (4 * n - 2) ^ 3 * (1 - (4 * n - 2)) ^ 4 +
      9736555176 * (4 * n - 2) ^ 4 * (1 - (4 * n - 2)) ^ 3 +
      5800077804 * (4 * n - 2) ^ 5 * (1 - (4 * n - 2)) ^ 2 +
      2047576786 * (4 * n - 2) ^ 6 * (1 - (4 * n - 2)) +
      345453127 * (4 * n - 2) ^ 7 := by
    unfold q2
    ring
  have hnonneg : 0 ≤ 11796480 * q2 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q2_quarter3 {n : ℝ}
    (hlo : (3 : ℝ) / 4 ≤ n) (hhi : n ≤ (4 : ℝ) / 4) : 0 ≤ q2 n := by
  have hz : 0 ≤ (4 * n - 3) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 3) := by linarith
  have hcert : 11796480 * q2 n =
      345453127 * (1 - (4 * n - 3)) ^ 7 +
      2788766992 * (4 * n - 3) * (1 - (4 * n - 3)) ^ 6 +
      10247219040 * (4 * n - 3) ^ 2 * (1 - (4 * n - 3)) ^ 5 +
      22136491264 * (4 * n - 3) ^ 3 * (1 - (4 * n - 3)) ^ 4 +
      30033262336 * (4 * n - 3) ^ 4 * (1 - (4 * n - 3)) ^ 3 +
      25262764032 * (4 * n - 3) ^ 5 * (1 - (4 * n - 3)) ^ 2 +
      12071387136 * (4 * n - 3) ^ 6 * (1 - (4 * n - 3)) +
      2511863808 * (4 * n - 3) ^ 7 := by
    unfold q2
    ring
  have hnonneg : 0 ≤ 11796480 * q2 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

theorem q2_nonneg {n : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1) : 0 ≤ q2 n := by
  rcases le_total n (1 / 4) with h | h
  · exact q2_quarter0 (by simpa using hn0) h
  rcases le_total n (2 / 4) with h2 | h2
  · exact q2_quarter1 h h2
  rcases le_total n (3 / 4) with h3 | h3
  · exact q2_quarter2 h2 h3
  · exact q2_quarter3 h3 (by simpa using hn1)

private theorem q3_quarter0 {n : ℝ}
    (hlo : (0 : ℝ) / 4 ≤ n) (hhi : n ≤ (1 : ℝ) / 4) : 0 ≤ q3 n := by
  have hz : 0 ≤ (4 * n - 0) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 0) := by linarith
  have hcert : 1966080 * q3 n =
      4898816 * (1 - (4 * n - 0)) ^ 7 +
      221659136 * (4 * n - 0) * (1 - (4 * n - 0)) ^ 6 +
      706062336 * (4 * n - 0) ^ 2 * (1 - (4 * n - 0)) ^ 5 +
      1022492928 * (4 * n - 0) ^ 3 * (1 - (4 * n - 0)) ^ 4 +
      906219840 * (4 * n - 0) ^ 4 * (1 - (4 * n - 0)) ^ 3 +
      541440384 * (4 * n - 0) ^ 5 * (1 - (4 * n - 0)) ^ 2 +
      200503936 * (4 * n - 0) ^ 6 * (1 - (4 * n - 0)) +
      33386881 * (4 * n - 0) ^ 7 := by
    unfold q3
    ring
  have hnonneg : 0 ≤ 1966080 * q3 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q3_quarter1 {n : ℝ}
    (hlo : (1 : ℝ) / 4 ≤ n) (hhi : n ≤ (2 : ℝ) / 4) : 0 ≤ q3 n := by
  have hz : 0 ≤ (4 * n - 1) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 1) := by linarith
  have hcert : 1966080 * q3 n =
      33386881 * (1 - (4 * n - 1)) ^ 7 +
      266912398 * (4 * n - 1) * (1 - (4 * n - 1)) ^ 6 +
      939891156 * (4 * n - 1) ^ 2 * (1 - (4 * n - 1)) ^ 5 +
      1826274520 * (4 * n - 1) ^ 3 * (1 - (4 * n - 1)) ^ 4 +
      2046373168 * (4 * n - 1) ^ 4 * (1 - (4 * n - 1)) ^ 3 +
      1309889184 * (4 * n - 1) ^ 5 * (1 - (4 * n - 1)) ^ 2 +
      444087744 * (4 * n - 1) ^ 6 * (1 - (4 * n - 1)) +
      61957248 * (4 * n - 1) ^ 7 := by
    unfold q3
    ring
  have hnonneg : 0 ≤ 1966080 * q3 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q3_quarter2 {n : ℝ}
    (hlo : (2 : ℝ) / 4 ≤ n) (hhi : n ≤ (3 : ℝ) / 4) : 0 ≤ q3 n := by
  have hz : 0 ≤ (4 * n - 2) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 2) := by linarith
  have hcert : 1966080 * q3 n =
      61957248 * (1 - (4 * n - 2)) ^ 7 +
      423313728 * (4 * n - 2) * (1 - (4 * n - 2)) ^ 6 +
      1185245088 * (4 * n - 2) ^ 2 * (1 - (4 * n - 2)) ^ 5 +
      1755283472 * (4 * n - 2) ^ 3 * (1 - (4 * n - 2)) ^ 4 +
      1492876376 * (4 * n - 2) ^ 4 * (1 - (4 * n - 2)) ^ 3 +
      750146748 * (4 * n - 2) ^ 5 * (1 - (4 * n - 2)) ^ 2 +
      221835614 * (4 * n - 2) ^ 6 * (1 - (4 * n - 2)) +
      34464779 * (4 * n - 2) ^ 7 := by
    unfold q3
    ring
  have hnonneg : 0 ≤ 1966080 * q3 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q3_quarter3 {n : ℝ}
    (hlo : (3 : ℝ) / 4 ≤ n) (hhi : n ≤ (4 : ℝ) / 4) : 0 ≤ q3 n := by
  have hz : 0 ≤ (4 * n - 3) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 3) := by linarith
  have hcert : 1966080 * q3 n =
      34464779 * (1 - (4 * n - 3)) ^ 7 +
      260671292 * (4 * n - 3) * (1 - (4 * n - 3)) ^ 6 +
      983160816 * (4 * n - 3) ^ 2 * (1 - (4 * n - 3)) ^ 5 +
      2348592384 * (4 * n - 3) ^ 3 * (1 - (4 * n - 3)) ^ 4 +
      3624720384 * (4 * n - 3) ^ 4 * (1 - (4 * n - 3)) ^ 3 +
      3448946688 * (4 * n - 3) ^ 5 * (1 - (4 * n - 3)) ^ 2 +
      1833213952 * (4 * n - 3) ^ 6 * (1 - (4 * n - 3)) +
      418643968 * (4 * n - 3) ^ 7 := by
    unfold q3
    ring
  have hnonneg : 0 ≤ 1966080 * q3 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

theorem q3_nonneg {n : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1) : 0 ≤ q3 n := by
  rcases le_total n (1 / 4) with h | h
  · exact q3_quarter0 (by simpa using hn0) h
  rcases le_total n (2 / 4) with h2 | h2
  · exact q3_quarter1 h h2
  rcases le_total n (3 / 4) with h3 | h3
  · exact q3_quarter2 h2 h3
  · exact q3_quarter3 h3 (by simpa using hn1)

private theorem q4_quarter0 {n : ℝ}
    (hlo : (0 : ℝ) / 4 ≤ n) (hhi : n ≤ (1 : ℝ) / 4) : 0 ≤ q4 n := by
  have hz : 0 ≤ (4 * n - 0) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 0) := by linarith
  have hcert : 3932160 * q4 n =
      16252928 * (1 - (4 * n - 0)) ^ 7 +
      917766144 * (4 * n - 0) * (1 - (4 * n - 0)) ^ 6 +
      2639790080 * (4 * n - 0) ^ 2 * (1 - (4 * n - 0)) ^ 5 +
      3039076352 * (4 * n - 0) ^ 3 * (1 - (4 * n - 0)) ^ 4 +
      1790831168 * (4 * n - 0) ^ 4 * (1 - (4 * n - 0)) ^ 3 +
      640144976 * (4 * n - 0) ^ 5 * (1 - (4 * n - 0)) ^ 2 +
      175832124 * (4 * n - 0) ^ 6 * (1 - (4 * n - 0)) +
      31029203 * (4 * n - 0) ^ 7 := by
    unfold q4
    ring
  have hnonneg : 0 ≤ 3932160 * q4 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q4_quarter1 {n : ℝ}
    (hlo : (1 : ℝ) / 4 ≤ n) (hhi : n ≤ (2 : ℝ) / 4) : 0 ≤ q4 n := by
  have hz : 0 ≤ (4 * n - 1) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 1) := by linarith
  have hcert : 3932160 * q4 n =
      31029203 * (1 - (4 * n - 1)) ^ 7 +
      258576718 * (4 * n - 1) * (1 - (4 * n - 1)) ^ 6 +
      1136612540 * (4 * n - 1) ^ 2 * (1 - (4 * n - 1)) ^ 5 +
      2748867992 * (4 * n - 1) ^ 3 * (1 - (4 * n - 1)) ^ 4 +
      3561439888 * (4 * n - 1) ^ 4 * (1 - (4 * n - 1)) ^ 3 +
      2478232736 * (4 * n - 1) ^ 5 * (1 - (4 * n - 1)) ^ 2 +
      873837888 * (4 * n - 1) ^ 6 * (1 - (4 * n - 1)) +
      122552448 * (4 * n - 1) ^ 7 := by
    unfold q4
    ring
  have hnonneg : 0 ≤ 3932160 * q4 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q4_quarter2 {n : ℝ}
    (hlo : (2 : ℝ) / 4 ≤ n) (hhi : n ≤ (3 : ℝ) / 4) : 0 ≤ q4 n := by
  have hz : 0 ≤ (4 * n - 2) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 2) := by linarith
  have hcert : 3932160 * q4 n =
      122552448 * (1 - (4 * n - 2)) ^ 7 +
      841896384 * (4 * n - 2) * (1 - (4 * n - 2)) ^ 6 +
      2286583712 * (4 * n - 2) ^ 2 * (1 - (4 * n - 2)) ^ 5 +
      3105299632 * (4 * n - 2) ^ 3 * (1 - (4 * n - 2)) ^ 4 +
      2201967128 * (4 * n - 2) ^ 4 * (1 - (4 * n - 2)) ^ 3 +
      774808916 * (4 * n - 2) ^ 5 * (1 - (4 * n - 2)) ^ 2 +
      117707134 * (4 * n - 2) ^ 6 * (1 - (4 * n - 2)) +
      12115865 * (4 * n - 2) ^ 7 := by
    unfold q4
    ring
  have hnonneg : 0 ≤ 3932160 * q4 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q4_quarter3 {n : ℝ}
    (hlo : (3 : ℝ) / 4 ≤ n) (hhi : n ≤ (4 : ℝ) / 4) : 0 ≤ q4 n := by
  have hz : 0 ≤ (4 * n - 3) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 3) := by linarith
  have hcert : 3932160 * q4 n =
      12115865 * (1 - (4 * n - 3)) ^ 7 +
      51914976 * (4 * n - 3) * (1 - (4 * n - 3)) ^ 6 +
      380055968 * (4 * n - 3) ^ 2 * (1 - (4 * n - 3)) ^ 5 +
      1876136192 * (4 * n - 3) ^ 3 * (1 - (4 * n - 3)) ^ 4 +
      4433662208 * (4 * n - 3) ^ 4 * (1 - (4 * n - 3)) ^ 3 +
      5374865408 * (4 * n - 3) ^ 5 * (1 - (4 * n - 3)) ^ 2 +
      3309060096 * (4 * n - 3) ^ 6 * (1 - (4 * n - 3)) +
      837287936 * (4 * n - 3) ^ 7 := by
    unfold q4
    ring
  have hnonneg : 0 ≤ 3932160 * q4 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

theorem q4_nonneg {n : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1) : 0 ≤ q4 n := by
  rcases le_total n (1 / 4) with h | h
  · exact q4_quarter0 (by simpa using hn0) h
  rcases le_total n (2 / 4) with h2 | h2
  · exact q4_quarter1 h h2
  rcases le_total n (3 / 4) with h3 | h3
  · exact q4_quarter2 h2 h3
  · exact q4_quarter3 h3 (by simpa using hn1)

/-- The multiplier in equation (15), with its exact rational coefficients. -/
def kappa (v b : ℝ) : ℝ :=
  let a := v - 1
  let s := b - 1;
  -(158 / 6) * (a - s) - (43 / 4) * a ^ 2 + (61 / 18) * a * s -
    (45 / 4) * s ^ 2 - (63 / 4) * s ^ 3 + (21 / 4) * a * s ^ 2 +
    (183 / 4) * a ^ 2 * s + (208 / 4) * a ^ 3 + (61 / 4) * s ^ 4 +
    (46 / 4) * a * s ^ 3 + (101 / 4) * a ^ 2 * s ^ 2 +
    (79 / 4) * a ^ 3 * s - (41 / 4) * a ^ 4

def theta (v b : ℝ) : ℝ :=
  let n := (2 - v - b) / 2
  let t := (v - b) / 2
  (n ^ 2 * (1 - n) * (105 + 5 * n) +
    t ^ 2 * (4 + 360 * n - 586 * n ^ 2) - 4 * t ^ 4) / 4

def zeroOrder (v b : ℝ) : ℝ :=
  let δ := 2 - v - b
  158 * (1 - δ ^ 2 / 4) * (v - b) ^ 2 +
    51 * δ * (v ^ 2 * (v - 1) ^ 2 + b ^ 2 * (b - 1) ^ 2) +
    6 * ((v - 1) * v * kappa v b + (b - 1) * b * kappa b v)

/-- The actual polynomial `F = c E₀ - Θ²` from equation (23). -/
def potential (v b : ℝ) : ℝ :=
  (2 / 5 - 3 * v * b / 10) * zeroOrder v b - theta v b ^ 2

def f0 (n : ℝ) : ℝ :=
  n ^ 3 * (1 - n) *
    (53511 * n ^ 4 - 151593 * n ^ 3 + 222537 * n ^ 2 - 83607 * n + 10256) / 240

def f1 (n : ℝ) : ℝ :=
  n * (19389 * n ^ 5 - 418926 * n ^ 4 + 523719 * n ^ 3 -
    289776 * n ^ 2 + 67782 * n + 10564) / 60

def f2 (n : ℝ) : ℝ :=
  (-1260129 * n ^ 4 + 1370598 * n ^ 3 - 451164 * n ^ 2 + 23442 * n + 74) / 60

def f3 (n : ℝ) : ℝ := (-12200 * n ^ 2 + 2601 * n + 75) / 10

def normalForm (n t : ℝ) : ℝ :=
  f0 n + f1 n * t ^ 2 + f2 n * t ^ 4 + f3 n * t ^ 6 - (23 / 5) * t ^ 8

theorem potential_normalForm (n t : ℝ) :
    potential (1 - n + t) (1 - n - t) = normalForm n t := by
  unfold potential zeroOrder theta kappa normalForm f0 f1 f2 f3
  ring

/-- Homogeneous Bernstein identity; clearing the denominator avoids any
division at the boundary `n = 1`. -/
theorem normalForm_certificate (n t : ℝ) :
    (1 - n) ^ 8 * normalForm n t =
      n ^ 3 * (1 - n) * q0 n * ((1 - n) ^ 2 - t ^ 2) ^ 4 +
      4 * n * (1 - n) * q1 n * t ^ 2 * ((1 - n) ^ 2 - t ^ 2) ^ 3 +
      6 * (1 - n) * q2 n * t ^ 4 * ((1 - n) ^ 2 - t ^ 2) ^ 2 +
      4 * (1 - n) * q3 n * t ^ 6 * ((1 - n) ^ 2 - t ^ 2) +
      (1 - n) * q4 n * t ^ 8 := by
  unfold normalForm f0 f1 f2 f3 q0 q1 q2 q3 q4
  ring

theorem normalForm_nonneg {n t : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1)
    (ht : t ^ 2 ≤ (1 - n) ^ 2) : 0 ≤ normalForm n t := by
  rcases eq_or_lt_of_le hn1 with hn | hn
  · subst n
    have ht0 : t = 0 := by nlinarith [sq_nonneg t]
    subst t
    norm_num [normalForm, f0, f1, f2, f3]
  have hd : 0 ≤ 1 - n := sub_nonneg.mpr hn1
  have hx : 0 ≤ (1 - n) ^ 2 - t ^ 2 := sub_nonneg.mpr ht
  have h0 := q0_nonneg hn0 hn1
  have h1 := q1_nonneg hn0 hn1
  have h2 := q2_nonneg hn0 hn1
  have h3 := q3_nonneg hn0 hn1
  have h4 := q4_nonneg hn0 hn1
  have hproduct : 0 ≤ (1 - n) ^ 8 * normalForm n t := by
    rw [normalForm_certificate]
    positivity
  exact nonneg_of_mul_nonneg_right hproduct (pow_pos (sub_pos.mpr hn) 8)

/-- Lemma 7.4 of the manuscript, including every boundary of its triangle. -/
theorem potential_nonneg {v b : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hsum : v + b ≤ 2) : 0 ≤ potential v b := by
  let n := (2 - v - b) / 2
  let t := (v - b) / 2
  have hn0 : 0 ≤ n := by dsimp [n]; linarith
  have hn1 : n ≤ 1 := by dsimp [n]; linarith
  have ht : t ^ 2 ≤ (1 - n) ^ 2 := by
    dsimp [n, t]
    nlinarith [mul_nonneg hv hb]
  have hvn : 1 - n + t = v := by dsimp [n, t]; ring
  have hbn : 1 - n - t = b := by dsimp [n, t]; ring
  have h := normalForm_nonneg hn0 hn1 ht
  rwa [← potential_normalForm, hvn, hbn] at h

end

end PositiveEinsteinFour.Potential

end OAI
