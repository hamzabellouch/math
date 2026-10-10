import Mathlib
import OAI.Combinatorics.KMedian.Analysis.CertificatePolynomials

namespace OAI

section
section
namespace MetricKMedian.Certificates
private theorem Tk_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 2)) :
    (1 / 10000) ≤ Tk X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 2) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Tk X - (1 / 10000) := by
    calc
      0 ≤ (1805480639441 / 4882812500000) * (X - 0) ^ 0 * ((1 / 2) - X) ^ 10 +
      (73114107677191 / 9765625000000) * (X - 0) ^ 1 * ((1 / 2) - X) ^ 9 +
      (1599146421551509 / 39062500000000) * (X - 0) ^ 2 * ((1 / 2) - X) ^ 8 +
      (342377561078167 / 3125000000000) * (X - 0) ^ 3 * ((1 / 2) - X) ^ 7 +
      (3334559213722287 / 19531250000000) * (X - 0) ^ 4 * ((1 / 2) - X) ^ 6 +
      (2590855721686419 / 15625000000000) * (X - 0) ^ 5 * ((1 / 2) - X) ^ 5 +
      (160573393740407 / 1562500000000) * (X - 0) ^ 6 * ((1 / 2) - X) ^ 4 +
      (12776957693747113 / 312500000000000) * (X - 0) ^ 7 * ((1 / 2) - X) ^ 3 +
      (6662818596154343 / 625000000000000) * (X - 0) ^ 8 * ((1 / 2) - X) ^ 2 +
      (2409954861851027 / 1250000000000000) * (X - 0) ^ 9 * ((1 / 2) - X) ^ 1 +
      (132419867113743 / 625000000000000) * (X - 0) ^ 10 * ((1 / 2) - X) ^ 0 := by positivity
      _ = Tk X - (1 / 10000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

private theorem Tk_lower_part1 {X : ℝ} (ha : (1 / 2) ≤ X) (hb : X ≤ 1) :
    (1 / 10000) ≤ Tk X := by
  have hu : 0 ≤ X - (1 / 2) := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Tk X - (1 / 10000) := by
    calc
      0 ≤ (132419867113743 / 625000000000000) * (X - (1 / 2)) ^ 0 * (1 - X) ^ 10 +
      (2886839822698693 / 1250000000000000) * (X - (1 / 2)) ^ 1 * (1 - X) ^ 9 +
      (220220022999221 / 15625000000000) * (X - (1 / 2)) ^ 2 * (1 - X) ^ 8 +
      (17328752263447299 / 312500000000000) * (X - (1 / 2)) ^ 3 * (1 - X) ^ 7 +
      (4394807238038073 / 31250000000000) * (X - (1 / 2)) ^ 4 * (1 - X) ^ 6 +
      (9008200454594741 / 39062500000000) * (X - (1 / 2)) ^ 5 * (1 - X) ^ 5 +
      (2384993556966093 / 9765625000000) * (X - (1 / 2)) ^ 6 * (1 - X) ^ 4 +
      (12761061088549709 / 78125000000000) * (X - (1 / 2)) ^ 7 * (1 - X) ^ 3 +
      (632232603598239 / 9765625000000) * (X - (1 / 2)) ^ 8 * (1 - X) ^ 2 +
      (50879711583183 / 3906250000000) * (X - (1 / 2)) ^ 9 * (1 - X) ^ 1 +
      (32595795117 / 39062500000) * (X - (1 / 2)) ^ 10 * (1 - X) ^ 0 := by positivity
      _ = Tk X - (1 / 10000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Tk_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 10000) ≤ Tk X := by
  by_cases ht0 : X ≤ (1 / 2)
  · exact Tk_lower_part0 ha ht0
  · have hl0 : (1 / 2) ≤ X := (lt_of_not_ge ht0).le
    exact Tk_lower_part1 hl0 hb

private theorem T1_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ T1 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ T1 X - (1 / 4000) := by
    calc
      0 ≤ (44877741 / 312500000) * (X - 0) ^ 0 * (1 - X) ^ 10 +
      (123804942226473 / 97656250000000) * (X - 0) ^ 1 * (1 - X) ^ 9 +
      (48641107020517 / 9765625000000) * (X - 0) ^ 2 * (1 - X) ^ 8 +
      (35853906645177401 / 3125000000000000) * (X - 0) ^ 3 * (1 - X) ^ 7 +
      (107381003477518643 / 6250000000000000) * (X - 0) ^ 4 * (1 - X) ^ 6 +
      (219116255716439199 / 12500000000000000) * (X - 0) ^ 5 * (1 - X) ^ 5 +
      (310376152073532481 / 25000000000000000) * (X - 0) ^ 6 * (1 - X) ^ 4 +
      (7613201630217909 / 1250000000000000) * (X - 0) ^ 7 * (1 - X) ^ 3 +
      (2011350239200609 / 1000000000000000) * (X - 0) ^ 8 * (1 - X) ^ 2 +
      (205349429 / 500000000) * (X - 0) ^ 9 * (1 - X) ^ 1 +
      (159 / 4000) * (X - 0) ^ 10 * (1 - X) ^ 0 := by positivity
      _ = T1 X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem T1_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ T1 X := by
  exact T1_lower_part0 ha hb

private theorem T2_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ T2 X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ T2 X - (1 / 4000) := by
    calc
      0 ≤ (2722592558549 / 19531250000000) * (X - 0) ^ 0 * (1 - X) ^ 9 +
      (21263759547693 / 15625000000000) * (X - 0) ^ 1 * (1 - X) ^ 8 +
      (7071626853427401 / 1250000000000000) * (X - 0) ^ 2 * (1 - X) ^ 7 +
      (33014244895018643 / 2500000000000000) * (X - 0) ^ 3 * (1 - X) ^ 6 +
      (95503164332439199 / 5000000000000000) * (X - 0) ^ 4 * (1 - X) ^ 5 +
      (177225629579532481 / 10000000000000000) * (X - 0) ^ 5 * (1 - X) ^ 4 +
      (5248520160917909 / 500000000000000) * (X - 0) ^ 6 * (1 - X) ^ 3 +
      (1517240450320609 / 400000000000000) * (X - 0) ^ 7 * (1 - X) ^ 2 +
      (747642107 / 1000000000) * (X - 0) ^ 8 * (1 - X) ^ 1 +
      (239 / 4000) * (X - 0) ^ 9 * (1 - X) ^ 0 := by positivity
      _ = T2 X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem T2_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ T2 X := by
  exact T2_lower_part0 ha hb

private theorem Q10_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q1 false X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Q1 false X - (1 / 4000) := by
    calc
      0 ≤ (401858697 / 7062500000) * (X - 0) ^ 0 * (1 - X) ^ 5 +
      (23821484731 / 56500000000) * (X - 0) ^ 1 * (1 - X) ^ 4 +
      (182224852041 / 141250000000) * (X - 0) ^ 2 * (1 - X) ^ 3 +
      (555959690843 / 282500000000) * (X - 0) ^ 3 * (1 - X) ^ 2 +
      (104694978609 / 70625000000) * (X - 0) ^ 4 * (1 - X) ^ 1 +
      (1014541 / 2260000) * (X - 0) ^ 5 * (1 - X) ^ 0 := by positivity
      _ = Q1 false X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Q10_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q1 false X := by
  exact Q10_lower_part0 ha hb

private theorem Q0u0_lower_part0 {X : ℝ} (ha : (65 / 226) ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q0 false (uZero false) X := by
  have hu : 0 ≤ X - (65 / 226) := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Q0 false (uZero false) X - (1 / 4000) := by
    calc
      0 ≤ (15377419780272212549 / 94905626541250000000) * (X - (65 / 226)) ^ 0 * (1 - X) ^ 4 +
      (2147829825253719941 / 1679745602500000000) * (X - (65 / 226)) ^ 1 * (1 - X) ^ 3 +
      (1249326404997110679 / 419936400625000000) * (X - (65 / 226)) ^ 2 * (1 - X) ^ 2 +
      (1158291035533895693 / 419936400625000000) * (X - (65 / 226)) ^ 3 * (1 - X) ^ 1 +
      (760033008677 / 839872801250) * (X - (65 / 226)) ^ 4 * (1 - X) ^ 0 := by positivity
      _ = Q0 false (uZero false) X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Q0u0_lower {X : ℝ} (ha : (65 / 226) ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q0 false (uZero false) X := by
  exact Q0u0_lower_part0 ha hb

private theorem Q0X0_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (65 / 226)) :
    (1 / 4000) ≤ Q0 false X X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (65 / 226) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Q0 false X X - (1 / 4000) := by
    calc
      0 ≤ (26616949523729557926 / 736512603759765625) * (X - 0) ^ 0 * ((65 / 226) - X) ^ 6 +
      (1108505996305909349273 / 5892100830078125000) * (X - 0) ^ 1 * ((65 / 226) - X) ^ 5 +
      (1070555096566927387931 / 2356840332031250000) * (X - 0) ^ 2 * ((65 / 226) - X) ^ 4 +
      (196730605689159043317 / 294605041503906250) * (X - 0) ^ 3 * ((65 / 226) - X) ^ 3 +
      (728676237597742428583 / 1178420166015625000) * (X - 0) ^ 4 * ((65 / 226) - X) ^ 2 +
      (15391598916307421235999 / 47136806640625000000) * (X - 0) ^ 5 * ((65 / 226) - X) ^ 1 +
      (1737648435170760018037 / 23568403320312500000) * (X - 0) ^ 6 * ((65 / 226) - X) ^ 0 := by positivity
      _ = Q0 false X X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Q0X0_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (65 / 226)) :
    (1 / 4000) ≤ Q0 false X X := by
  exact Q0X0_lower_part0 ha hb

private theorem Yh0_lower_part0 {X : ℝ} (ha : (1 / 2) ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Y false X-h X := by
  have hu : 0 ≤ X - (1 / 2) := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Y false X-h X - (1 / 4000) := by
    calc
      0 ≤ (25276579 / 100000000) * (X - (1 / 2)) ^ 0 * (1 - X) ^ 5 +
      (93121463 / 8000000) * (X - (1 / 2)) ^ 1 * (1 - X) ^ 4 +
      (9818867161 / 200000000) * (X - (1 / 2)) ^ 2 * (1 - X) ^ 3 +
      (802390057 / 10000000) * (X - (1 / 2)) ^ 3 * (1 - X) ^ 2 +
      (117132303 / 2000000) * (X - (1 / 2)) ^ 4 * (1 - X) ^ 1 +
      (10027 / 625) * (X - (1 / 2)) ^ 5 * (1 - X) ^ 0 := by positivity
      _ = Y false X-h X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Yh0_lower {X : ℝ} (ha : (1 / 2) ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Y false X-h X := by
  exact Yh0_lower_part0 ha hb

private theorem Yquarter0_lower_part0 {X : ℝ} (ha : (1 / 2) ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Y false X-1/4 := by
  have hu : 0 ≤ X - (1 / 2) := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Y false X-1/4 - (1 / 4000) := by
    calc
      0 ≤ (166076579 / 100000000) * (X - (1 / 2)) ^ 0 * (1 - X) ^ 5 +
      (99521463 / 8000000) * (X - (1 / 2)) ^ 1 * (1 - X) ^ 4 +
      (7066867161 / 200000000) * (X - (1 / 2)) ^ 2 * (1 - X) ^ 3 +
      (483990057 / 10000000) * (X - (1 / 2)) ^ 3 * (1 - X) ^ 2 +
      (64652303 / 2000000) * (X - (1 / 2)) ^ 4 * (1 - X) ^ 1 +
      (5307 / 625) * (X - (1 / 2)) ^ 5 * (1 - X) ^ 0 := by positivity
      _ = Y false X-1/4 - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Yquarter0_lower {X : ℝ} (ha : (1 / 2) ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Y false X-1/4 := by
  exact Yquarter0_lower_part0 ha hb

private theorem Yph0_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 8)) :
    (1 / 4000) ≤ Yprime X+(13/25)*k X-h X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 8) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Yprime X+(13/25)*k X-h X - (1 / 4000) := by
    calc
      0 ≤ (4142260224 / 390625) * (X - 0) ^ 0 * ((1 / 8) - X) ^ 6 +
      (4079468032 / 78125) * (X - 0) ^ 1 * ((1 / 8) - X) ^ 5 +
      (205031442336 / 1953125) * (X - 0) ^ 2 * ((1 / 8) - X) ^ 4 +
      (214663557868 / 1953125) * (X - 0) ^ 3 * ((1 / 8) - X) ^ 3 +
      (123009872643 / 1953125) * (X - 0) ^ 4 * ((1 / 8) - X) ^ 2 +
      (145957888689 / 7812500) * (X - 0) ^ 5 * ((1 / 8) - X) ^ 1 +
      (70194064247 / 31250000) * (X - 0) ^ 6 * ((1 / 8) - X) ^ 0 := by positivity
      _ = Yprime X+(13/25)*k X-h X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

private theorem Yph0_lower_part1 {X : ℝ} (ha : (1 / 8) ≤ X) (hb : X ≤ (1 / 4)) :
    (1 / 4000) ≤ Yprime X+(13/25)*k X-h X := by
  have hu : 0 ≤ X - (1 / 8) := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 4) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Yprime X+(13/25)*k X-h X - (1 / 4000) := by
    calc
      0 ≤ (70194064247 / 31250000) * (X - (1 / 8)) ^ 0 * ((1 / 4) - X) ^ 6 +
      (16156076013 / 1953125) * (X - (1 / 8)) ^ 1 * ((1 / 4) - X) ^ 5 +
      (85371567387 / 7812500) * (X - (1 / 8)) ^ 2 * ((1 / 4) - X) ^ 4 +
      (11777178856 / 1953125) * (X - (1 / 8)) ^ 3 * ((1 / 4) - X) ^ 3 +
      (608045697 / 390625) * (X - (1 / 8)) ^ 4 * ((1 / 4) - X) ^ 2 +
      (1663295888 / 1953125) * (X - (1 / 8)) ^ 5 * ((1 / 4) - X) ^ 1 +
      (826315684 / 1953125) * (X - (1 / 8)) ^ 6 * ((1 / 4) - X) ^ 0 := by positivity
      _ = Yprime X+(13/25)*k X-h X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

private theorem Yph0_lower_part2 {X : ℝ} (ha : (1 / 4) ≤ X) (hb : X ≤ (1 / 2)) :
    (1 / 4000) ≤ Yprime X+(13/25)*k X-h X := by
  have hu : 0 ≤ X - (1 / 4) := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 2) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Yprime X+(13/25)*k X-h X - (1 / 4000) := by
    calc
      0 ≤ (206578921 / 31250000) * (X - (1 / 4)) ^ 0 * ((1 / 2) - X) ^ 6 +
      (1443386317 / 15625000) * (X - (1 / 4)) ^ 1 * ((1 / 2) - X) ^ 5 +
      (922683183 / 1562500) * (X - (1 / 4)) ^ 2 * ((1 / 2) - X) ^ 4 +
      (6204085811 / 3906250) * (X - (1 / 4)) ^ 3 * ((1 / 2) - X) ^ 3 +
      (4000195644 / 1953125) * (X - (1 / 4)) ^ 4 * ((1 / 2) - X) ^ 2 +
      (2483278992 / 1953125) * (X - (1 / 4)) ^ 5 * ((1 / 2) - X) ^ 1 +
      (599298656 / 1953125) * (X - (1 / 4)) ^ 6 * ((1 / 2) - X) ^ 0 := by positivity
      _ = Yprime X+(13/25)*k X-h X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Yph0_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 2)) :
    (1 / 4000) ≤ Yprime X+(13/25)*k X-h X := by
  by_cases ht0 : X ≤ (1 / 8)
  · exact Yph0_lower_part0 ha ht0
  · have hl0 : (1 / 8) ≤ X := (lt_of_not_ge ht0).le
    by_cases ht1 : X ≤ (1 / 4)
    · exact Yph0_lower_part1 hl0 ht1
    · have hl1 : (1 / 4) ≤ X := (lt_of_not_ge ht1).le
      exact Yph0_lower_part2 hl1 hb

private theorem Ypquarter0_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 2)) :
    (1 / 4000) ≤ Yprime X-1/4 := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ (1 / 2) - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Yprime X-1/4 - (1 / 4000) := by
    calc
      0 ≤ (3614194 / 390625) * (X - 0) ^ 0 * ((1 / 2) - X) ^ 6 +
      (33933571 / 781250) * (X - 0) ^ 1 * ((1 / 2) - X) ^ 5 +
      (1298227673 / 15625000) * (X - 0) ^ 2 * ((1 / 2) - X) ^ 4 +
      (529319783 / 6250000) * (X - 0) ^ 3 * ((1 / 2) - X) ^ 3 +
      (401955531 / 7812500) * (X - 0) ^ 4 * ((1 / 2) - X) ^ 2 +
      (76385189 / 3906250) * (X - 0) ^ 5 * ((1 / 2) - X) ^ 1 +
      (15229833 / 3906250) * (X - 0) ^ 6 * ((1 / 2) - X) ^ 0 := by positivity
      _ = Yprime X-1/4 - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Ypquarter0_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ (1 / 2)) :
    (1 / 4000) ≤ Yprime X-1/4 := by
  exact Ypquarter0_lower_part0 ha hb

private theorem Q11_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q1 true X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Q1 true X - (1 / 4000) := by
    calc
      0 ≤ (83130855038973 / 195312500000000) * (X - 0) ^ 0 * (1 - X) ^ 8 +
      (58074341534074523 / 17187500000000000) * (X - 0) ^ 1 * (1 - X) ^ 7 +
      (161754312088447973 / 13750000000000000) * (X - 0) ^ 2 * (1 - X) ^ 6 +
      (1614659272241560729 / 68750000000000000) * (X - 0) ^ 3 * (1 - X) ^ 5 +
      (8096263173487397231 / 275000000000000000) * (X - 0) ^ 4 * (1 - X) ^ 4 +
      (653455827646010503 / 27500000000000000) * (X - 0) ^ 5 * (1 - X) ^ 3 +
      (132875110518381699 / 11000000000000000) * (X - 0) ^ 6 * (1 - X) ^ 2 +
      (311852255063 / 88000000000) * (X - 0) ^ 7 * (1 - X) ^ 1 +
      (2533 / 5500) * (X - 0) ^ 8 * (1 - X) ^ 0 := by positivity
      _ = Q1 true X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Q11_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q1 true X := by
  exact Q11_lower_part0 ha hb

private theorem Q0u1_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q0 true (uZero true) X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Q0 true (uZero true) X - (1 / 4000) := by
    calc
      0 ≤ (1073963 / 62500000) * (X - 0) ^ 0 * (1 - X) ^ 4 +
      (288567027 / 2750000000) * (X - 0) ^ 1 * (1 - X) ^ 3 +
      (293860011 / 1375000000) * (X - 0) ^ 2 * (1 - X) ^ 2 +
      (497217619 / 2750000000) * (X - 0) ^ 3 * (1 - X) ^ 1 +
      (2389 / 44000) * (X - 0) ^ 4 * (1 - X) ^ 0 := by positivity
      _ = Q0 true (uZero true) X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Q0u1_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Q0 true (uZero true) X := by
  exact Q0u1_lower_part0 ha hb

private theorem Yh1_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Y true X-h X := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Y true X-h X - (1 / 4000) := by
    calc
      0 ≤ (7196017 / 200000000) * (X - 0) ^ 0 * (1 - X) ^ 5 +
      (156780239 / 1600000000) * (X - 0) ^ 1 * (1 - X) ^ 4 +
      (312742177 / 640000000) * (X - 0) ^ 2 * (1 - X) ^ 3 +
      (1963273751 / 1600000000) * (X - 0) ^ 3 * (1 - X) ^ 2 +
      (770208811 / 640000000) * (X - 0) ^ 4 * (1 - X) ^ 1 +
      (3261 / 8000) * (X - 0) ^ 5 * (1 - X) ^ 0 := by positivity
      _ = Y true X-h X - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Yh1_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Y true X-h X := by
  exact Yh1_lower_part0 ha hb

private theorem Yquarter1_lower_part0 {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Y true X-1/4 := by
  have hu : 0 ≤ X - 0 := sub_nonneg.mpr ha
  have hv : 0 ≤ 1 - X := sub_nonneg.mpr hb
  have hcert : 0 ≤ Y true X-1/4 - (1 / 4000) := by
    calc
      0 ≤ (35996017 / 200000000) * (X - 0) ^ 0 * (1 - X) ^ 5 +
      (1308780239 / 1600000000) * (X - 0) ^ 1 * (1 - X) ^ 4 +
      (965542177 / 640000000) * (X - 0) ^ 2 * (1 - X) ^ 3 +
      (2315273751 / 1600000000) * (X - 0) ^ 3 * (1 - X) ^ 2 +
      (475808811 / 640000000) * (X - 0) ^ 4 * (1 - X) ^ 1 +
      (1373 / 8000) * (X - 0) ^ 5 * (1 - X) ^ 0 := by positivity
      _ = Y true X-1/4 - (1 / 4000) := by
        dsimp only [p, v, k, h, pSeries, aSeries, bit, d, H, c, N, l, hh, uZero, uOne, Tk, T1, T2, Q0, Q1, Y, Yprime, B0, B1, B2, discr, total]
        norm_num
        ring
  linarith only [hcert]

theorem Yquarter1_lower {X : ℝ} (ha : 0 ≤ X) (hb : X ≤ 1) :
    (1 / 4000) ≤ Y true X-1/4 := by
  exact Yquarter1_lower_part0 ha hb


end MetricKMedian.Certificates
end
end

end OAI
