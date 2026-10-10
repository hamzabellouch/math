import OAI.Geometry.EinsteinFour.Boundary
import OAI.Geometry.EinsteinFour.Matrix
import OAI.Geometry.EinsteinFour.Potential
import OAI.Geometry.EinsteinFour.QuarticClosed
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OAI


section

/-! The finite matrix certificates for the quadratic coupling estimate. -/

namespace PositiveEinsteinFour.Quadratic

open Potential

noncomputable section

def weight (v b : ℝ) : ℝ := (1 - 3 * (v - b) / 8) ^ 2
def Pk (v b : ℝ) : ℝ := 300 * weight v b + 272 * (2 - v - b)
def Pl (v b : ℝ) : ℝ := 35 * weight v b * v
def P0 (v b : ℝ) : ℝ := Pk v b + 51 * v
def K2 (v b σ : ℝ) : ℝ :=
  weight v b * (42 + 3 * b ^ 2 + 10 * v ^ 2) -
    (17 / 10) * (6 * (σ * v ^ 2 + b ^ 2 - v - b) - 26 * (2 - v - b))
def K1 (v b σ : ℝ) : ℝ :=
  5 * K2 v b σ + weight v b * (300 * v * σ + 140 * v ^ 2) +
    272 * (2 - v - b) * v * σ
def K12 (v b σ : ℝ) : ℝ :=
  weight v b * (75 * v + 35 * v ^ 2 * σ) + 68 * (2 - v - b) * v
def A11 (v b σ : ℝ) : ℝ :=
  P0 v b * (v * K1 v b σ - 5 * kappa v b) - (1 + σ) * v ^ 2 * (Pk v b) ^ 2
def A22 (v b σ : ℝ) : ℝ :=
  P0 v b * (v * K2 v b σ - kappa v b) - (1 + σ) * v ^ 2 * (Pl v b) ^ 2
def A12 (v b σ : ℝ) : ℝ :=
  P0 v b * v * K12 v b σ - (1 + σ) * v ^ 2 * Pk v b * Pl v b

private theorem combine_quadratic_sums (L : List (ℝ × ℝ × ℝ × ℝ)) (x y : ℝ) :
    (L.map (fun a => a.1 * a.2.2.2)).sum * x ^ 2 +
      2 * (L.map (fun a => a.2.2.1 * a.2.2.2)).sum * x * y +
      (L.map (fun a => a.2.1 * a.2.2.2)).sum * y ^ 2 =
      (L.map (fun a => (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rcases a with ⟨r, h, q, w⟩
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    ring

private theorem combine_quadratic_nonneg (L : List (ℝ × ℝ × ℝ × ℝ)) (x y : ℝ)
    (h : L.Forall (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2)) :
    0 ≤ (L.map (fun a => a.1 * a.2.2.2)).sum * x ^ 2 +
      2 * (L.map (fun a => a.2.2.1 * a.2.2.2)).sum * x * y +
      (L.map (fun a => a.2.1 * a.2.2.2)).sum * y ^ 2 := by
  rw [combine_quadratic_sums]
  apply List.sum_nonneg
  intro t ht
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
  exact (List.forall_iff_forall_mem.mp h) a ha

private theorem A_OSC_hc0 (x y : ℝ) : 0 ≤ (17252710400 * x ^ 2 + 2 * 0 * x * y + 3450542080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 17252710400 3450542080 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc1 (x y : ℝ) : 0 ≤ (158056814080 * x ^ 2 + 2 * 0 * x * y + 31611362816 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 158056814080 31611362816 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc2 (x y : ℝ) : 0 ≤ (479164067840 * x ^ 2 + 2 * 16412221440 * x * y + 108962590720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 479164067840 108962590720 16412221440
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc3 (x y : ℝ) : 0 ≤ (715874263040 * x ^ 2 + 2 * 75585669120 * x * y + 202056613888 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 715874263040 202056613888 75585669120
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc4 (x y : ℝ) : 0 ≤ (621716700160 * x ^ 2 + 2 * 139843399680 * x * y + 228817943552 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 621716700160 228817943552 139843399680
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc5 (x y : ℝ) : 0 ≤ (359540042240 * x ^ 2 + 2 * 131761336320 * x * y + 163584352768 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 359540042240 163584352768 131761336320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc6 (x y : ℝ) : 0 ≤ (155718743040 * x ^ 2 + 2 * 65896980480 * x * y + 71196115968 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 155718743040 71196115968 65896980480
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc7 (x y : ℝ) : 0 ≤ (46921236480 * x ^ 2 + 2 * 16428533760 * x * y + 16728219648 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 46921236480 16728219648 16428533760
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc8 (x y : ℝ) : 0 ≤ (6540134400 * x ^ 2 + 2 * 1622937600 * x * y + 1553356800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6540134400 1553356800 1622937600
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc9 (x y : ℝ) : 0 ≤ (115729146880 * x ^ 2 + 2 * 0 * x * y + 23145829376 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 115729146880 23145829376 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc10 (x y : ℝ) : 0 ≤ (868924433920 * x ^ 2 + 2 * 32824442880 * x * y + 200044441088 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 868924433920 200044441088 32824442880
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc11 (x y : ℝ) : 0 ≤ (2199990382080 * x ^ 2 + 2 * 228584908800 * x * y + 618105681408 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2199990382080 618105681408 228584908800
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc12 (x y : ℝ) : 0 ≤ (2777259973120 * x ^ 2 + 2 * 569280360960 * x * y + 981187455488 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2777259973120 981187455488 569280360960
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc13 (x y : ℝ) : 0 ≤ (2096990801920 * x ^ 2 + 2 * 678715292160 * x * y + 893889413120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2096990801920 893889413120 678715292160
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc14 (x y : ℝ) : 0 ≤ (1065675640320 * x ^ 2 + 2 * 413946155520 * x * y + 469378856448 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1065675640320 469378856448 413946155520
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc15 (x y : ℝ) : 0 ≤ (352909432320 * x ^ 2 + 2 * 122889991680 * x * y + 129556729344 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 352909432320 129556729344 122889991680
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc16 (x y : ℝ) : 0 ≤ (53759715840 * x ^ 2 + 2 * 14139233280 * x * y + 14086900224 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 53759715840 14086900224 14139233280
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc17 (x y : ℝ) : 0 ≤ (317429568480 * x ^ 2 + 2 * 16412221440 * x * y + 76615690848 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 317429568480 76615690848 16412221440
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc18 (x y : ℝ) : 0 ≤ (2004721901600 * x ^ 2 + 2 * 230412810240 * x * y + 580514306464 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2004721901600 580514306464 230412810240
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc19 (x y : ℝ) : 0 ≤ (4293146296480 * x ^ 2 + 2 * 870472316160 * x * y + 1510341325856 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4293146296480 1510341325856 870472316160
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc20 (x y : ℝ) : 0 ≤ (4635392834400 * x ^ 2 + 2 * 1402601150880 * x * y + 1912483495776 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4635392834400 1912483495776 1402601150880
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc21 (x y : ℝ) : 0 ≤ (2977183602080 * x ^ 2 + 2 * 1087456210560 * x * y + 1280348492704 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2977183602080 1280348492704 1087456210560
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc22 (x y : ℝ) : 0 ≤ (1143655466560 * x ^ 2 + 2 * 395407510560 * x * y + 430117149632 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1143655466560 430117149632 395407510560
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc23 (x y : ℝ) : 0 ≤ (196010735520 * x ^ 2 + 2 * 54080723520 * x * y + 55809442464 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 196010735520 55809442464 54080723520
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc24 (x y : ℝ) : 0 ≤ (480178552960 * x ^ 2 + 2 * 77413570560 * x * y + 156379793024 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 480178552960 156379793024 77413570560
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc25 (x y : ℝ) : 0 ≤ (2603039483520 * x ^ 2 + 2 * 592477148160 * x * y + 964724061312 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2603039483520 964724061312 592477148160
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc26 (x y : ℝ) : 0 ≤ (4741503929600 * x ^ 2 + 2 * 1453216430880 * x * y + 1974404593792 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4741503929600 1974404593792 1453216430880
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc27 (x y : ℝ) : 0 ≤ (4260670908800 * x ^ 2 + 2 * 1528657741440 * x * y + 1830675210112 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4260670908800 1830675210112 1528657741440
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc28 (x y : ℝ) : 0 ≤ (2038681949120 * x ^ 2 + 2 * 709121944800 * x * y + 787479157024 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2038681949120 787479157024 709121944800
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc29 (x y : ℝ) : 0 ≤ (410625264960 * x ^ 2 + 2 * 118617056640 * x * y + 125658517536 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 410625264960 125658517536 118617056640
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc30 (x y : ℝ) : 0 ≤ (454056140000 * x ^ 2 + 2 * 151441793280 * x * y + 204476183392 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 454056140000 204476183392 151441793280
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc31 (x y : ℝ) : 0 ≤ (2133392931580 * x ^ 2 + 2 * 754683896160 * x * y + 962254704716 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2133392931580 962254704716 754683896160
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc32 (x y : ℝ) : 0 ≤ (3203939071020 * x ^ 2 + 2 * 1212283815210 * x * y + 1428624843972 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3203939071020 1428624843972 1212283815210
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc33 (x y : ℝ) : 0 ≤ (2117912965930 * x ^ 2 + 2 * 765276701850 * x * y + 851201225066 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2117912965930 851201225066 765276701850
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc34 (x y : ℝ) : 0 ≤ (534168603450 * x ^ 2 + 2 * 163163833200 * x * y + 174955046445 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 534168603450 174955046445 163163833200
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc35 (x y : ℝ) : 0 ≤ (287785218300 * x ^ 2 + 2 * 157114660320 * x * y + 169619374668 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 287785218300 169619374668 157114660320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc36 (x y : ℝ) : 0 ≤ (1135771302200 * x ^ 2 + 2 * 514070353620 * x * y + 565947886312 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1135771302200 565947886312 514070353620
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc37 (x y : ℝ) : 0 ≤ (1246501965850 * x ^ 2 + 2 * 496822876110 * x * y + 537161025002 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1246501965850 537161025002 496822876110
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc38 (x y : ℝ) : 0 ≤ (434606482500 * x ^ 2 + 2 * 144110577600 * x * y + 153232839840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 434606482500 153232839840 144110577600
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc39 (x y : ℝ) : 0 ≤ (124979975180 * x ^ 2 + 2 * 91037244330 * x * y + 85773208228 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 124979975180 85773208228 91037244330
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc40 (x y : ℝ) : 0 ≤ (364138717400 * x ^ 2 + 2 * 179606086830 * x * y + 180175149520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 364138717400 180175149520 179606086830
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc41 (x y : ℝ) : 0 ≤ (210441454290 * x ^ 2 + 2 * 79790093280 * x * y + 81685041804 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 210441454290 81685041804 79790093280
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc42 (x y : ℝ) : 0 ≤ (34535039080 * x ^ 2 + 2 * 27884020410 * x * y + 24024832496 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 34535039080 24024832496 27884020410
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc43 (x y : ℝ) : 0 ≤ (52679027520 * x ^ 2 + 2 * 25311712320 * x * y + 23874369804 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 52679027520 23874369804 25311712320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OSC_hc44 (x y : ℝ) : 0 ≤ (4509563160 * x ^ 2 + 2 * 3520992240 * x * y + 2849739891 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4509563160 2849739891 3520992240
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem A_OSC_entry11 (z w : ℝ) : 92160 * A11 (z + w) w 1 =
      17252710400 * ((1 - z - w) ^ 8) +
      158056814080 * (w * (1 - z - w) ^ 7) +
      479164067840 * (w ^ 2 * (1 - z - w) ^ 6) +
      715874263040 * (w ^ 3 * (1 - z - w) ^ 5) +
      621716700160 * (w ^ 4 * (1 - z - w) ^ 4) +
      359540042240 * (w ^ 5 * (1 - z - w) ^ 3) +
      155718743040 * (w ^ 6 * (1 - z - w) ^ 2) +
      46921236480 * (w ^ 7 * (1 - z - w)) +
      6540134400 * (w ^ 8) +
      115729146880 * (z * (1 - z - w) ^ 7) +
      868924433920 * (z * w * (1 - z - w) ^ 6) +
      2199990382080 * (z * w ^ 2 * (1 - z - w) ^ 5) +
      2777259973120 * (z * w ^ 3 * (1 - z - w) ^ 4) +
      2096990801920 * (z * w ^ 4 * (1 - z - w) ^ 3) +
      1065675640320 * (z * w ^ 5 * (1 - z - w) ^ 2) +
      352909432320 * (z * w ^ 6 * (1 - z - w)) +
      53759715840 * (z * w ^ 7) +
      317429568480 * (z ^ 2 * (1 - z - w) ^ 6) +
      2004721901600 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      4293146296480 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      4635392834400 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      2977183602080 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      1143655466560 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      196010735520 * (z ^ 2 * w ^ 6) +
      480178552960 * (z ^ 3 * (1 - z - w) ^ 5) +
      2603039483520 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      4741503929600 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      4260670908800 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      2038681949120 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      410625264960 * (z ^ 3 * w ^ 5) +
      454056140000 * (z ^ 4 * (1 - z - w) ^ 4) +
      2133392931580 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      3203939071020 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      2117912965930 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      534168603450 * (z ^ 4 * w ^ 4) +
      287785218300 * (z ^ 5 * (1 - z - w) ^ 3) +
      1135771302200 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      1246501965850 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      434606482500 * (z ^ 5 * w ^ 3) +
      124979975180 * (z ^ 6 * (1 - z - w) ^ 2) +
      364138717400 * (z ^ 6 * w * (1 - z - w)) +
      210441454290 * (z ^ 6 * w ^ 2) +
      34535039080 * (z ^ 7 * (1 - z - w)) +
      52679027520 * (z ^ 7 * w) +
      4509563160 * (z ^ 8) := by
  simp only [A11, P0, Pk, K1, K2, weight, kappa]
  ring

private theorem A_OSC_entry22 (z w : ℝ) : 92160 * A22 (z + w) w 1 =
      3450542080 * ((1 - z - w) ^ 8) +
      31611362816 * (w * (1 - z - w) ^ 7) +
      108962590720 * (w ^ 2 * (1 - z - w) ^ 6) +
      202056613888 * (w ^ 3 * (1 - z - w) ^ 5) +
      228817943552 * (w ^ 4 * (1 - z - w) ^ 4) +
      163584352768 * (w ^ 5 * (1 - z - w) ^ 3) +
      71196115968 * (w ^ 6 * (1 - z - w) ^ 2) +
      16728219648 * (w ^ 7 * (1 - z - w)) +
      1553356800 * (w ^ 8) +
      23145829376 * (z * (1 - z - w) ^ 7) +
      200044441088 * (z * w * (1 - z - w) ^ 6) +
      618105681408 * (z * w ^ 2 * (1 - z - w) ^ 5) +
      981187455488 * (z * w ^ 3 * (1 - z - w) ^ 4) +
      893889413120 * (z * w ^ 4 * (1 - z - w) ^ 3) +
      469378856448 * (z * w ^ 5 * (1 - z - w) ^ 2) +
      129556729344 * (z * w ^ 6 * (1 - z - w)) +
      14086900224 * (z * w ^ 7) +
      76615690848 * (z ^ 2 * (1 - z - w) ^ 6) +
      580514306464 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      1510341325856 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      1912483495776 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      1280348492704 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      430117149632 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      55809442464 * (z ^ 2 * w ^ 6) +
      156379793024 * (z ^ 3 * (1 - z - w) ^ 5) +
      964724061312 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      1974404593792 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      1830675210112 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      787479157024 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      125658517536 * (z ^ 3 * w ^ 5) +
      204476183392 * (z ^ 4 * (1 - z - w) ^ 4) +
      962254704716 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      1428624843972 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      851201225066 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      174955046445 * (z ^ 4 * w ^ 4) +
      169619374668 * (z ^ 5 * (1 - z - w) ^ 3) +
      565947886312 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      537161025002 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      153232839840 * (z ^ 5 * w ^ 3) +
      85773208228 * (z ^ 6 * (1 - z - w) ^ 2) +
      180175149520 * (z ^ 6 * w * (1 - z - w)) +
      81685041804 * (z ^ 6 * w ^ 2) +
      24024832496 * (z ^ 7 * (1 - z - w)) +
      23874369804 * (z ^ 7 * w) +
      2849739891 * (z ^ 8) := by
  simp only [A22, P0, Pk, Pl, K2, weight, kappa]
  ring

private theorem A_OSC_entry12 (z w : ℝ) : 92160 * A12 (z + w) w 1 =
      16412221440 * (w ^ 2 * (1 - z - w) ^ 6) +
      75585669120 * (w ^ 3 * (1 - z - w) ^ 5) +
      139843399680 * (w ^ 4 * (1 - z - w) ^ 4) +
      131761336320 * (w ^ 5 * (1 - z - w) ^ 3) +
      65896980480 * (w ^ 6 * (1 - z - w) ^ 2) +
      16428533760 * (w ^ 7 * (1 - z - w)) +
      1622937600 * (w ^ 8) +
      32824442880 * (z * w * (1 - z - w) ^ 6) +
      228584908800 * (z * w ^ 2 * (1 - z - w) ^ 5) +
      569280360960 * (z * w ^ 3 * (1 - z - w) ^ 4) +
      678715292160 * (z * w ^ 4 * (1 - z - w) ^ 3) +
      413946155520 * (z * w ^ 5 * (1 - z - w) ^ 2) +
      122889991680 * (z * w ^ 6 * (1 - z - w)) +
      14139233280 * (z * w ^ 7) +
      16412221440 * (z ^ 2 * (1 - z - w) ^ 6) +
      230412810240 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      870472316160 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      1402601150880 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      1087456210560 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      395407510560 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      54080723520 * (z ^ 2 * w ^ 6) +
      77413570560 * (z ^ 3 * (1 - z - w) ^ 5) +
      592477148160 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      1453216430880 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      1528657741440 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      709121944800 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      118617056640 * (z ^ 3 * w ^ 5) +
      151441793280 * (z ^ 4 * (1 - z - w) ^ 4) +
      754683896160 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      1212283815210 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      765276701850 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      163163833200 * (z ^ 4 * w ^ 4) +
      157114660320 * (z ^ 5 * (1 - z - w) ^ 3) +
      514070353620 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      496822876110 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      144110577600 * (z ^ 5 * w ^ 3) +
      91037244330 * (z ^ 6 * (1 - z - w) ^ 2) +
      179606086830 * (z ^ 6 * w * (1 - z - w)) +
      79790093280 * (z ^ 6 * w ^ 2) +
      27884020410 * (z ^ 7 * (1 - z - w)) +
      25311712320 * (z ^ 7 * w) +
      3520992240 * (z ^ 8) := by
  simp only [A12, P0, Pk, Pl, K12, weight]
  ring
private def A_OSC_data (z w : ℝ) : List (ℝ × ℝ × ℝ × ℝ) :=
  [(17252710400, 3450542080, 0, (1 - z - w) ^ 8),
  (158056814080, 31611362816, 0, w * (1 - z - w) ^ 7),
  (479164067840, 108962590720, 16412221440, w ^ 2 * (1 - z - w) ^ 6),
  (715874263040, 202056613888, 75585669120, w ^ 3 * (1 - z - w) ^ 5),
  (621716700160, 228817943552, 139843399680, w ^ 4 * (1 - z - w) ^ 4),
  (359540042240, 163584352768, 131761336320, w ^ 5 * (1 - z - w) ^ 3),
  (155718743040, 71196115968, 65896980480, w ^ 6 * (1 - z - w) ^ 2),
  (46921236480, 16728219648, 16428533760, w ^ 7 * (1 - z - w)),
  (6540134400, 1553356800, 1622937600, w ^ 8),
  (115729146880, 23145829376, 0, z * (1 - z - w) ^ 7),
  (868924433920, 200044441088, 32824442880, z * w * (1 - z - w) ^ 6),
  (2199990382080, 618105681408, 228584908800, z * w ^ 2 * (1 - z - w) ^ 5),
  (2777259973120, 981187455488, 569280360960, z * w ^ 3 * (1 - z - w) ^ 4),
  (2096990801920, 893889413120, 678715292160, z * w ^ 4 * (1 - z - w) ^ 3),
  (1065675640320, 469378856448, 413946155520, z * w ^ 5 * (1 - z - w) ^ 2),
  (352909432320, 129556729344, 122889991680, z * w ^ 6 * (1 - z - w)),
  (53759715840, 14086900224, 14139233280, z * w ^ 7),
  (317429568480, 76615690848, 16412221440, z ^ 2 * (1 - z - w) ^ 6),
  (2004721901600, 580514306464, 230412810240, z ^ 2 * w * (1 - z - w) ^ 5),
  (4293146296480, 1510341325856, 870472316160, z ^ 2 * w ^ 2 * (1 - z - w) ^ 4),
  (4635392834400, 1912483495776, 1402601150880, z ^ 2 * w ^ 3 * (1 - z - w) ^ 3),
  (2977183602080, 1280348492704, 1087456210560, z ^ 2 * w ^ 4 * (1 - z - w) ^ 2),
  (1143655466560, 430117149632, 395407510560, z ^ 2 * w ^ 5 * (1 - z - w)),
  (196010735520, 55809442464, 54080723520, z ^ 2 * w ^ 6),
  (480178552960, 156379793024, 77413570560, z ^ 3 * (1 - z - w) ^ 5),
  (2603039483520, 964724061312, 592477148160, z ^ 3 * w * (1 - z - w) ^ 4),
  (4741503929600, 1974404593792, 1453216430880, z ^ 3 * w ^ 2 * (1 - z - w) ^ 3),
  (4260670908800, 1830675210112, 1528657741440, z ^ 3 * w ^ 3 * (1 - z - w) ^ 2),
  (2038681949120, 787479157024, 709121944800, z ^ 3 * w ^ 4 * (1 - z - w)),
  (410625264960, 125658517536, 118617056640, z ^ 3 * w ^ 5),
  (454056140000, 204476183392, 151441793280, z ^ 4 * (1 - z - w) ^ 4),
  (2133392931580, 962254704716, 754683896160, z ^ 4 * w * (1 - z - w) ^ 3),
  (3203939071020, 1428624843972, 1212283815210, z ^ 4 * w ^ 2 * (1 - z - w) ^ 2),
  (2117912965930, 851201225066, 765276701850, z ^ 4 * w ^ 3 * (1 - z - w)),
  (534168603450, 174955046445, 163163833200, z ^ 4 * w ^ 4),
  (287785218300, 169619374668, 157114660320, z ^ 5 * (1 - z - w) ^ 3),
  (1135771302200, 565947886312, 514070353620, z ^ 5 * w * (1 - z - w) ^ 2),
  (1246501965850, 537161025002, 496822876110, z ^ 5 * w ^ 2 * (1 - z - w)),
  (434606482500, 153232839840, 144110577600, z ^ 5 * w ^ 3),
  (124979975180, 85773208228, 91037244330, z ^ 6 * (1 - z - w) ^ 2),
  (364138717400, 180175149520, 179606086830, z ^ 6 * w * (1 - z - w)),
  (210441454290, 81685041804, 79790093280, z ^ 6 * w ^ 2),
  (34535039080, 24024832496, 27884020410, z ^ 7 * (1 - z - w)),
  (52679027520, 23874369804, 25311712320, z ^ 7 * w),
  (4509563160, 2849739891, 3520992240, z ^ 8)]

private theorem A_OSC_entry11_list (z w : ℝ) :
    92160 * A11 (z + w) w 1 = ((A_OSC_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [A_OSC_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_OSC_entry11 z w

private theorem A_OSC_entry22_list (z w : ℝ) :
    92160 * A22 (z + w) w 1 = ((A_OSC_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [A_OSC_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_OSC_entry22 z w

private theorem A_OSC_entry12_list (z w : ℝ) :
    92160 * A12 (z + w) w 1 = ((A_OSC_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [A_OSC_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_OSC_entry12 z w

private theorem A_OSC {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ A11 (z + w) w 1 * x ^ 2 + 2 * A12 (z + w) w 1 * x * y + A22 (z + w) w 1 * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (A_OSC_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (A_OSC_hc0 x y) (by positivity),
      mul_nonneg (A_OSC_hc1 x y) (by positivity),
      mul_nonneg (A_OSC_hc2 x y) (by positivity),
      mul_nonneg (A_OSC_hc3 x y) (by positivity),
      mul_nonneg (A_OSC_hc4 x y) (by positivity),
      mul_nonneg (A_OSC_hc5 x y) (by positivity),
      mul_nonneg (A_OSC_hc6 x y) (by positivity),
      mul_nonneg (A_OSC_hc7 x y) (by positivity),
      mul_nonneg (A_OSC_hc8 x y) (by positivity),
      mul_nonneg (A_OSC_hc9 x y) (by positivity),
      mul_nonneg (A_OSC_hc10 x y) (by positivity),
      mul_nonneg (A_OSC_hc11 x y) (by positivity),
      mul_nonneg (A_OSC_hc12 x y) (by positivity),
      mul_nonneg (A_OSC_hc13 x y) (by positivity),
      mul_nonneg (A_OSC_hc14 x y) (by positivity),
      mul_nonneg (A_OSC_hc15 x y) (by positivity),
      mul_nonneg (A_OSC_hc16 x y) (by positivity),
      mul_nonneg (A_OSC_hc17 x y) (by positivity),
      mul_nonneg (A_OSC_hc18 x y) (by positivity),
      mul_nonneg (A_OSC_hc19 x y) (by positivity),
      mul_nonneg (A_OSC_hc20 x y) (by positivity),
      mul_nonneg (A_OSC_hc21 x y) (by positivity),
      mul_nonneg (A_OSC_hc22 x y) (by positivity),
      mul_nonneg (A_OSC_hc23 x y) (by positivity),
      mul_nonneg (A_OSC_hc24 x y) (by positivity),
      mul_nonneg (A_OSC_hc25 x y) (by positivity),
      mul_nonneg (A_OSC_hc26 x y) (by positivity),
      mul_nonneg (A_OSC_hc27 x y) (by positivity),
      mul_nonneg (A_OSC_hc28 x y) (by positivity),
      mul_nonneg (A_OSC_hc29 x y) (by positivity),
      mul_nonneg (A_OSC_hc30 x y) (by positivity),
      mul_nonneg (A_OSC_hc31 x y) (by positivity),
      mul_nonneg (A_OSC_hc32 x y) (by positivity),
      mul_nonneg (A_OSC_hc33 x y) (by positivity),
      mul_nonneg (A_OSC_hc34 x y) (by positivity),
      mul_nonneg (A_OSC_hc35 x y) (by positivity),
      mul_nonneg (A_OSC_hc36 x y) (by positivity),
      mul_nonneg (A_OSC_hc37 x y) (by positivity),
      mul_nonneg (A_OSC_hc38 x y) (by positivity),
      mul_nonneg (A_OSC_hc39 x y) (by positivity),
      mul_nonneg (A_OSC_hc40 x y) (by positivity),
      mul_nonneg (A_OSC_hc41 x y) (by positivity),
      mul_nonneg (A_OSC_hc42 x y) (by positivity),
      mul_nonneg (A_OSC_hc43 x y) (by positivity),
      mul_nonneg (A_OSC_hc44 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (A_OSC_data z w) x y hcoeff
  rw [← A_OSC_entry11_list, ← A_OSC_entry12_list, ← A_OSC_entry22_list] at hpos
  nlinarith only [hpos]

private theorem A_OCW_hc0 (x y : ℝ) : 0 ≤ (1078294400 * x ^ 2 + 2 * 0 * x * y + 215658880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1078294400 215658880 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc1 (x y : ℝ) : 0 ≤ (13917313600 * x ^ 2 + 2 * 0 * x * y + 2783462720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 13917313600 2783462720 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc2 (x y : ℝ) : 0 ≤ (49146252600 * x ^ 2 + 2 * 0 * x * y + 9829250520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 49146252600 9829250520 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc3 (x y : ℝ) : 0 ≤ (83212031200 * x ^ 2 + 2 * 0 * x * y + 16642406240 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 83212031200 16642406240 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc4 (x y : ℝ) : 0 ≤ (79111415000 * x ^ 2 + 2 * 0 * x * y + 15822283000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 79111415000 15822283000 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc5 (x y : ℝ) : 0 ≤ (44620627200 * x ^ 2 + 2 * 0 * x * y + 8924125440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 44620627200 8924125440 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc6 (x y : ℝ) : 0 ≤ (15005417000 * x ^ 2 + 2 * 0 * x * y + 3001083400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 15005417000 3001083400 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc7 (x y : ℝ) : 0 ≤ (2617132000 * x ^ 2 + 2 * 0 * x * y + 523426400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2617132000 523426400 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc8 (x y : ℝ) : 0 ≤ (25725000 * x ^ 2 + 2 * 0 * x * y + 5145000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 25725000 5145000 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc9 (x y : ℝ) : 0 ≤ (9878550880 * x ^ 2 + 2 * 0 * x * y + 1975710176 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 9878550880 1975710176 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc10 (x y : ℝ) : 0 ≤ (80325318880 * x ^ 2 + 2 * 0 * x * y + 16065063776 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 80325318880 16065063776 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc11 (x y : ℝ) : 0 ≤ (212593326440 * x ^ 2 + 2 * 0 * x * y + 42518665288 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 212593326440 42518665288 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc12 (x y : ℝ) : 0 ≤ (273006125160 * x ^ 2 + 2 * 0 * x * y + 54601225032 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 273006125160 54601225032 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc13 (x y : ℝ) : 0 ≤ (193148912140 * x ^ 2 + 2 * 0 * x * y + 38629782428 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 193148912140 38629782428 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc14 (x y : ℝ) : 0 ≤ (79438591940 * x ^ 2 + 2 * 0 * x * y + 15887718388 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 79438591940 15887718388 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc15 (x y : ℝ) : 0 ≤ (18951498020 * x ^ 2 + 2 * 0 * x * y + 3790299604 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 18951498020 3790299604 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc16 (x y : ℝ) : 0 ≤ (1802251500 * x ^ 2 + 2 * 0 * x * y + 360450300 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1802251500 360450300 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc17 (x y : ℝ) : 0 ≤ (29947754240 * x ^ 2 + 2 * 1025763840 * x * y + 6810161920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 29947754240 6810161920 1025763840
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc18 (x y : ℝ) : 0 ≤ (173140576320 * x ^ 2 + 2 * 5926095360 * x * y + 39368991552 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 173140576320 39368991552 5926095360
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc19 (x y : ℝ) : 0 ≤ (339403212520 * x ^ 2 + 2 * 14666927040 * x * y + 79614184136 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 339403212520 79614184136 14666927040
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc20 (x y : ℝ) : 0 ≤ (314227263920 * x ^ 2 + 2 * 19876347360 * x * y + 78746530672 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 314227263920 78746530672 19876347360
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc21 (x y : ℝ) : 0 ≤ (152504665740 * x ^ 2 + 2 * 15542982090 * x * y + 42935318820 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 152504665740 42935318820 15542982090
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc22 (x y : ℝ) : 0 ≤ (40732801840 * x ^ 2 + 2 * 6648736500 * x * y + 13465549568 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 40732801840 13465549568 6648736500
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc23 (x y : ℝ) : 0 ≤ (5091974580 * x ^ 2 + 2 * 1215506250 * x * y + 1990799916 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 5091974580 1990799916 1215506250
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc24 (x y : ℝ) : 0 ≤ (44742141440 * x ^ 2 + 2 * 4724104320 * x * y + 12628538368 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 44742141440 12628538368 4724104320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc25 (x y : ℝ) : 0 ≤ (187411560640 * x ^ 2 + 2 * 22382176320 * x * y + 54903231680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 187411560640 54903231680 22382176320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc26 (x y : ℝ) : 0 ≤ (262932340440 * x ^ 2 + 2 * 43625998440 * x * y + 86519885784 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 262932340440 86519885784 43625998440
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc27 (x y : ℝ) : 0 ≤ (164590050440 * x ^ 2 + 2 * 43648558200 * x * y + 66851908744 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 164590050440 66851908744 43648558200
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc28 (x y : ℝ) : 0 ≤ (50113080370 * x ^ 2 + 2 * 22390181010 * x * y + 27423589106 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 50113080370 27423589106 22390181010
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc29 (x y : ℝ) : 0 ≤ (7160879370 * x ^ 2 + 2 * 4709549250 * x * y + 5091858474 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7160879370 5091858474 4709549250
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc30 (x y : ℝ) : 0 ≤ (38857293760 * x ^ 2 + 2 * 8740212480 * x * y + 14301121472 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 38857293760 14301121472 8740212480
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc31 (x y : ℝ) : 0 ≤ (118017851200 * x ^ 2 + 2 * 32472273600 * x * y + 47708529728 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 118017851200 47708529728 32472273600
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc32 (x y : ℝ) : 0 ≤ (117056427560 * x ^ 2 + 2 * 46520580960 * x * y + 57667847848 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 117056427560 57667847848 46520580960
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc33 (x y : ℝ) : 0 ≤ (49587064400 * x ^ 2 + 2 * 30367398240 * x * y + 32036261728 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 49587064400 32036261728 30367398240
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc34 (x y : ℝ) : 0 ≤ (9113859330 * x ^ 2 + 2 * 7600748400 * x * y + 7273386021 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 9113859330 7273386021 7600748400
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc35 (x y : ℝ) : 0 ≤ (22471252640 * x ^ 2 + 2 * 8235083520 * x * y + 10224022048 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 22471252640 10224022048 8235083520
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc36 (x y : ℝ) : 0 ≤ (50993360160 * x ^ 2 + 2 * 22384716480 * x * y + 25396796064 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 50993360160 25396796064 22384716480
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc37 (x y : ℝ) : 0 ≤ (37459172080 * x ^ 2 + 2 * 20830874760 * x * y + 21138872528 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 37459172080 21138872528 20830874760
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc38 (x y : ℝ) : 0 ≤ (10303385520 * x ^ 2 + 2 * 6595187400 * x * y + 6146705184 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 10303385520 6146705184 6595187400
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc39 (x y : ℝ) : 0 ≤ (9732421440 * x ^ 2 + 2 * 4118561280 * x * y + 4449757248 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 9732421440 4449757248 4118561280
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc40 (x y : ℝ) : 0 ≤ (16407245760 * x ^ 2 + 2 * 7250840640 * x * y + 7342115520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 16407245760 7342115520 7250840640
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc41 (x y : ℝ) : 0 ≤ (7378946280 * x ^ 2 + 2 * 3269365200 * x * y + 3066141096 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7378946280 3066141096 3269365200
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc42 (x y : ℝ) : 0 ≤ (2932577280 * x ^ 2 + 2 * 1026783360 * x * y + 1045513728 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2932577280 1045513728 1026783360
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc43 (x y : ℝ) : 0 ≤ (2752747200 * x ^ 2 + 2 * 882316800 * x * y + 838008000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2752747200 838008000 882316800
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_OCW_hc44 (x y : ℝ) : 0 ≤ (408758400 * x ^ 2 + 2 * 101433600 * x * y + 97084800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 408758400 97084800 101433600
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem A_OCW_entry11 (z w : ℝ) : 5760 * A11 z (z + 2 * w) 1 =
      1078294400 * ((1 - z - w) ^ 8) +
      13917313600 * (w * (1 - z - w) ^ 7) +
      49146252600 * (w ^ 2 * (1 - z - w) ^ 6) +
      83212031200 * (w ^ 3 * (1 - z - w) ^ 5) +
      79111415000 * (w ^ 4 * (1 - z - w) ^ 4) +
      44620627200 * (w ^ 5 * (1 - z - w) ^ 3) +
      15005417000 * (w ^ 6 * (1 - z - w) ^ 2) +
      2617132000 * (w ^ 7 * (1 - z - w)) +
      25725000 * (w ^ 8) +
      9878550880 * (z * (1 - z - w) ^ 7) +
      80325318880 * (z * w * (1 - z - w) ^ 6) +
      212593326440 * (z * w ^ 2 * (1 - z - w) ^ 5) +
      273006125160 * (z * w ^ 3 * (1 - z - w) ^ 4) +
      193148912140 * (z * w ^ 4 * (1 - z - w) ^ 3) +
      79438591940 * (z * w ^ 5 * (1 - z - w) ^ 2) +
      18951498020 * (z * w ^ 6 * (1 - z - w)) +
      1802251500 * (z * w ^ 7) +
      29947754240 * (z ^ 2 * (1 - z - w) ^ 6) +
      173140576320 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      339403212520 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      314227263920 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      152504665740 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      40732801840 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      5091974580 * (z ^ 2 * w ^ 6) +
      44742141440 * (z ^ 3 * (1 - z - w) ^ 5) +
      187411560640 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      262932340440 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      164590050440 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      50113080370 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      7160879370 * (z ^ 3 * w ^ 5) +
      38857293760 * (z ^ 4 * (1 - z - w) ^ 4) +
      118017851200 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      117056427560 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      49587064400 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      9113859330 * (z ^ 4 * w ^ 4) +
      22471252640 * (z ^ 5 * (1 - z - w) ^ 3) +
      50993360160 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      37459172080 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      10303385520 * (z ^ 5 * w ^ 3) +
      9732421440 * (z ^ 6 * (1 - z - w) ^ 2) +
      16407245760 * (z ^ 6 * w * (1 - z - w)) +
      7378946280 * (z ^ 6 * w ^ 2) +
      2932577280 * (z ^ 7 * (1 - z - w)) +
      2752747200 * (z ^ 7 * w) +
      408758400 * (z ^ 8) := by
  simp only [A11, P0, Pk, K1, K2, weight, kappa]
  ring

private theorem A_OCW_entry22 (z w : ℝ) : 5760 * A22 z (z + 2 * w) 1 =
      215658880 * ((1 - z - w) ^ 8) +
      2783462720 * (w * (1 - z - w) ^ 7) +
      9829250520 * (w ^ 2 * (1 - z - w) ^ 6) +
      16642406240 * (w ^ 3 * (1 - z - w) ^ 5) +
      15822283000 * (w ^ 4 * (1 - z - w) ^ 4) +
      8924125440 * (w ^ 5 * (1 - z - w) ^ 3) +
      3001083400 * (w ^ 6 * (1 - z - w) ^ 2) +
      523426400 * (w ^ 7 * (1 - z - w)) +
      5145000 * (w ^ 8) +
      1975710176 * (z * (1 - z - w) ^ 7) +
      16065063776 * (z * w * (1 - z - w) ^ 6) +
      42518665288 * (z * w ^ 2 * (1 - z - w) ^ 5) +
      54601225032 * (z * w ^ 3 * (1 - z - w) ^ 4) +
      38629782428 * (z * w ^ 4 * (1 - z - w) ^ 3) +
      15887718388 * (z * w ^ 5 * (1 - z - w) ^ 2) +
      3790299604 * (z * w ^ 6 * (1 - z - w)) +
      360450300 * (z * w ^ 7) +
      6810161920 * (z ^ 2 * (1 - z - w) ^ 6) +
      39368991552 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      79614184136 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      78746530672 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      42935318820 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      13465549568 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      1990799916 * (z ^ 2 * w ^ 6) +
      12628538368 * (z ^ 3 * (1 - z - w) ^ 5) +
      54903231680 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      86519885784 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      66851908744 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      27423589106 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      5091858474 * (z ^ 3 * w ^ 5) +
      14301121472 * (z ^ 4 * (1 - z - w) ^ 4) +
      47708529728 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      57667847848 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      32036261728 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      7273386021 * (z ^ 4 * w ^ 4) +
      10224022048 * (z ^ 5 * (1 - z - w) ^ 3) +
      25396796064 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      21138872528 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      6146705184 * (z ^ 5 * w ^ 3) +
      4449757248 * (z ^ 6 * (1 - z - w) ^ 2) +
      7342115520 * (z ^ 6 * w * (1 - z - w)) +
      3066141096 * (z ^ 6 * w ^ 2) +
      1045513728 * (z ^ 7 * (1 - z - w)) +
      838008000 * (z ^ 7 * w) +
      97084800 * (z ^ 8) := by
  simp only [A22, P0, Pk, Pl, K2, weight, kappa]
  ring

private theorem A_OCW_entry12 (z w : ℝ) : 5760 * A12 z (z + 2 * w) 1 =
      1025763840 * (z ^ 2 * (1 - z - w) ^ 6) +
      5926095360 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      14666927040 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      19876347360 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      15542982090 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      6648736500 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      1215506250 * (z ^ 2 * w ^ 6) +
      4724104320 * (z ^ 3 * (1 - z - w) ^ 5) +
      22382176320 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      43625998440 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      43648558200 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      22390181010 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      4709549250 * (z ^ 3 * w ^ 5) +
      8740212480 * (z ^ 4 * (1 - z - w) ^ 4) +
      32472273600 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      46520580960 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      30367398240 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      7600748400 * (z ^ 4 * w ^ 4) +
      8235083520 * (z ^ 5 * (1 - z - w) ^ 3) +
      22384716480 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      20830874760 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      6595187400 * (z ^ 5 * w ^ 3) +
      4118561280 * (z ^ 6 * (1 - z - w) ^ 2) +
      7250840640 * (z ^ 6 * w * (1 - z - w)) +
      3269365200 * (z ^ 6 * w ^ 2) +
      1026783360 * (z ^ 7 * (1 - z - w)) +
      882316800 * (z ^ 7 * w) +
      101433600 * (z ^ 8) := by
  simp only [A12, P0, Pk, Pl, K12, weight]
  ring
private def A_OCW_data (z w : ℝ) : List (ℝ × ℝ × ℝ × ℝ) :=
  [(1078294400, 215658880, 0, (1 - z - w) ^ 8),
  (13917313600, 2783462720, 0, w * (1 - z - w) ^ 7),
  (49146252600, 9829250520, 0, w ^ 2 * (1 - z - w) ^ 6),
  (83212031200, 16642406240, 0, w ^ 3 * (1 - z - w) ^ 5),
  (79111415000, 15822283000, 0, w ^ 4 * (1 - z - w) ^ 4),
  (44620627200, 8924125440, 0, w ^ 5 * (1 - z - w) ^ 3),
  (15005417000, 3001083400, 0, w ^ 6 * (1 - z - w) ^ 2),
  (2617132000, 523426400, 0, w ^ 7 * (1 - z - w)),
  (25725000, 5145000, 0, w ^ 8),
  (9878550880, 1975710176, 0, z * (1 - z - w) ^ 7),
  (80325318880, 16065063776, 0, z * w * (1 - z - w) ^ 6),
  (212593326440, 42518665288, 0, z * w ^ 2 * (1 - z - w) ^ 5),
  (273006125160, 54601225032, 0, z * w ^ 3 * (1 - z - w) ^ 4),
  (193148912140, 38629782428, 0, z * w ^ 4 * (1 - z - w) ^ 3),
  (79438591940, 15887718388, 0, z * w ^ 5 * (1 - z - w) ^ 2),
  (18951498020, 3790299604, 0, z * w ^ 6 * (1 - z - w)),
  (1802251500, 360450300, 0, z * w ^ 7),
  (29947754240, 6810161920, 1025763840, z ^ 2 * (1 - z - w) ^ 6),
  (173140576320, 39368991552, 5926095360, z ^ 2 * w * (1 - z - w) ^ 5),
  (339403212520, 79614184136, 14666927040, z ^ 2 * w ^ 2 * (1 - z - w) ^ 4),
  (314227263920, 78746530672, 19876347360, z ^ 2 * w ^ 3 * (1 - z - w) ^ 3),
  (152504665740, 42935318820, 15542982090, z ^ 2 * w ^ 4 * (1 - z - w) ^ 2),
  (40732801840, 13465549568, 6648736500, z ^ 2 * w ^ 5 * (1 - z - w)),
  (5091974580, 1990799916, 1215506250, z ^ 2 * w ^ 6),
  (44742141440, 12628538368, 4724104320, z ^ 3 * (1 - z - w) ^ 5),
  (187411560640, 54903231680, 22382176320, z ^ 3 * w * (1 - z - w) ^ 4),
  (262932340440, 86519885784, 43625998440, z ^ 3 * w ^ 2 * (1 - z - w) ^ 3),
  (164590050440, 66851908744, 43648558200, z ^ 3 * w ^ 3 * (1 - z - w) ^ 2),
  (50113080370, 27423589106, 22390181010, z ^ 3 * w ^ 4 * (1 - z - w)),
  (7160879370, 5091858474, 4709549250, z ^ 3 * w ^ 5),
  (38857293760, 14301121472, 8740212480, z ^ 4 * (1 - z - w) ^ 4),
  (118017851200, 47708529728, 32472273600, z ^ 4 * w * (1 - z - w) ^ 3),
  (117056427560, 57667847848, 46520580960, z ^ 4 * w ^ 2 * (1 - z - w) ^ 2),
  (49587064400, 32036261728, 30367398240, z ^ 4 * w ^ 3 * (1 - z - w)),
  (9113859330, 7273386021, 7600748400, z ^ 4 * w ^ 4),
  (22471252640, 10224022048, 8235083520, z ^ 5 * (1 - z - w) ^ 3),
  (50993360160, 25396796064, 22384716480, z ^ 5 * w * (1 - z - w) ^ 2),
  (37459172080, 21138872528, 20830874760, z ^ 5 * w ^ 2 * (1 - z - w)),
  (10303385520, 6146705184, 6595187400, z ^ 5 * w ^ 3),
  (9732421440, 4449757248, 4118561280, z ^ 6 * (1 - z - w) ^ 2),
  (16407245760, 7342115520, 7250840640, z ^ 6 * w * (1 - z - w)),
  (7378946280, 3066141096, 3269365200, z ^ 6 * w ^ 2),
  (2932577280, 1045513728, 1026783360, z ^ 7 * (1 - z - w)),
  (2752747200, 838008000, 882316800, z ^ 7 * w),
  (408758400, 97084800, 101433600, z ^ 8)]

private theorem A_OCW_entry11_list (z w : ℝ) :
    5760 * A11 z (z + 2 * w) 1 = ((A_OCW_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [A_OCW_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_OCW_entry11 z w

private theorem A_OCW_entry22_list (z w : ℝ) :
    5760 * A22 z (z + 2 * w) 1 = ((A_OCW_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [A_OCW_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_OCW_entry22 z w

private theorem A_OCW_entry12_list (z w : ℝ) :
    5760 * A12 z (z + 2 * w) 1 = ((A_OCW_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [A_OCW_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_OCW_entry12 z w

private theorem A_OCW {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ A11 z (z + 2 * w) 1 * x ^ 2 + 2 * A12 z (z + 2 * w) 1 * x * y + A22 z (z + 2 * w) 1 * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (A_OCW_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (A_OCW_hc0 x y) (by positivity),
      mul_nonneg (A_OCW_hc1 x y) (by positivity),
      mul_nonneg (A_OCW_hc2 x y) (by positivity),
      mul_nonneg (A_OCW_hc3 x y) (by positivity),
      mul_nonneg (A_OCW_hc4 x y) (by positivity),
      mul_nonneg (A_OCW_hc5 x y) (by positivity),
      mul_nonneg (A_OCW_hc6 x y) (by positivity),
      mul_nonneg (A_OCW_hc7 x y) (by positivity),
      mul_nonneg (A_OCW_hc8 x y) (by positivity),
      mul_nonneg (A_OCW_hc9 x y) (by positivity),
      mul_nonneg (A_OCW_hc10 x y) (by positivity),
      mul_nonneg (A_OCW_hc11 x y) (by positivity),
      mul_nonneg (A_OCW_hc12 x y) (by positivity),
      mul_nonneg (A_OCW_hc13 x y) (by positivity),
      mul_nonneg (A_OCW_hc14 x y) (by positivity),
      mul_nonneg (A_OCW_hc15 x y) (by positivity),
      mul_nonneg (A_OCW_hc16 x y) (by positivity),
      mul_nonneg (A_OCW_hc17 x y) (by positivity),
      mul_nonneg (A_OCW_hc18 x y) (by positivity),
      mul_nonneg (A_OCW_hc19 x y) (by positivity),
      mul_nonneg (A_OCW_hc20 x y) (by positivity),
      mul_nonneg (A_OCW_hc21 x y) (by positivity),
      mul_nonneg (A_OCW_hc22 x y) (by positivity),
      mul_nonneg (A_OCW_hc23 x y) (by positivity),
      mul_nonneg (A_OCW_hc24 x y) (by positivity),
      mul_nonneg (A_OCW_hc25 x y) (by positivity),
      mul_nonneg (A_OCW_hc26 x y) (by positivity),
      mul_nonneg (A_OCW_hc27 x y) (by positivity),
      mul_nonneg (A_OCW_hc28 x y) (by positivity),
      mul_nonneg (A_OCW_hc29 x y) (by positivity),
      mul_nonneg (A_OCW_hc30 x y) (by positivity),
      mul_nonneg (A_OCW_hc31 x y) (by positivity),
      mul_nonneg (A_OCW_hc32 x y) (by positivity),
      mul_nonneg (A_OCW_hc33 x y) (by positivity),
      mul_nonneg (A_OCW_hc34 x y) (by positivity),
      mul_nonneg (A_OCW_hc35 x y) (by positivity),
      mul_nonneg (A_OCW_hc36 x y) (by positivity),
      mul_nonneg (A_OCW_hc37 x y) (by positivity),
      mul_nonneg (A_OCW_hc38 x y) (by positivity),
      mul_nonneg (A_OCW_hc39 x y) (by positivity),
      mul_nonneg (A_OCW_hc40 x y) (by positivity),
      mul_nonneg (A_OCW_hc41 x y) (by positivity),
      mul_nonneg (A_OCW_hc42 x y) (by positivity),
      mul_nonneg (A_OCW_hc43 x y) (by positivity),
      mul_nonneg (A_OCW_hc44 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (A_OCW_data z w) x y hcoeff
  rw [← A_OCW_entry11_list, ← A_OCW_entry12_list, ← A_OCW_entry22_list] at hpos
  nlinarith only [hpos]

private theorem A_SCU_hc0 (x y : ℝ) : 0 ≤ (4509563160 * x ^ 2 + 2 * 3520992240 * x * y + 2849739891 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4509563160 2849739891 3520992240
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc1 (x y : ℝ) : 0 ≤ (37617971480 * x ^ 2 + 2 * 28451855430 * x * y + 21571005760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 37617971480 21571005760 28451855430
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc2 (x y : ℝ) : 0 ≤ (146560501980 * x ^ 2 + 2 * 95012089470 * x * y + 68596421076 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 146560501980 68596421076 95012089470
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc3 (x y : ℝ) : 0 ≤ (331315496820 * x ^ 2 + 2 * 170479080720 * x * y + 118256665572 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 331315496820 118256665572 170479080720
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc4 (x y : ℝ) : 0 ≤ (455902264600 * x ^ 2 + 2 * 178515443880 * x * y + 119430509432 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 455902264600 119430509432 178515443880
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc5 (x y : ℝ) : 0 ≤ (379173161760 * x ^ 2 + 2 * 110060120160 * x * y + 71195690784 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 379173161760 71195690784 110060120160
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc6 (x y : ℝ) : 0 ≤ (179673110880 * x ^ 2 + 2 * 37856028960 * x * y + 23831782752 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 179673110880 23831782752 37856028960
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc7 (x y : ℝ) : 0 ≤ (41075910080 * x ^ 2 + 2 * 6256419840 * x * y + 3911982784 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 41075910080 3911982784 6256419840
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc8 (x y : ℝ) : 0 ≤ (2537099520 * x ^ 2 + 2 * 342921600 * x * y + 222426624 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2537099520 222426624 342921600
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc9 (x y : ℝ) : 0 ≤ (52679027520 * x ^ 2 + 2 * 25311712320 * x * y + 23874369804 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 52679027520 23874369804 25311712320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc10 (x y : ℝ) : 0 ≤ (373367667880 * x ^ 2 + 2 * 174757885650 * x * y + 154066027736 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 373367667880 154066027736 174757885650
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc11 (x y : ℝ) : 0 ≤ (1191145005080 * x ^ 2 + 2 * 484981146540 * x * y + 409293155608 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1191145005080 409293155608 484981146540
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc12 (x y : ℝ) : 0 ≤ (2126124752020 * x ^ 2 + 2 * 696933879840 * x * y + 571538732324 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2126124752020 571538732324 696933879840
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc13 (x y : ℝ) : 0 ≤ (2204808746080 * x ^ 2 + 2 * 555405130080 * x * y + 446225043104 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2204808746080 446225043104 555405130080
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc14 (x y : ℝ) : 0 ≤ (1280803135040 * x ^ 2 + 2 * 241674700320 * x * y + 191088676672 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1280803135040 191088676672 241674700320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc15 (x y : ℝ) : 0 ≤ (365211583360 * x ^ 2 + 2 * 51921040320 * x * y + 40445269376 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 365211583360 40445269376 51921040320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc16 (x y : ℝ) : 0 ≤ (33652689600 * x ^ 2 + 2 * 4233427200 * x * y + 3179636160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 33652689600 3179636160 4233427200
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc17 (x y : ℝ) : 0 ≤ (210441454290 * x ^ 2 + 2 * 79790093280 * x * y + 81685041804 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 210441454290 81685041804 79790093280
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc18 (x y : ℝ) : 0 ≤ (1278795485630 * x ^ 2 + 2 * 460658243250 * x * y + 443059476646 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1278795485630 443059476646 460658243250
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc19 (x y : ℝ) : 0 ≤ (3365406669920 * x ^ 2 + 2 * 1031460650910 * x * y + 958117102192 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3365406669920 958117102192 1031460650910
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc20 (x y : ℝ) : 0 ≤ (4700562690960 * x ^ 2 + 2 * 1138553971200 * x * y + 1037759846544 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4700562690960 1037759846544 1138553971200
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc21 (x y : ℝ) : 0 ≤ (3524452184960 * x ^ 2 + 2 * 649777594320 * x * y + 582438051232 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3524452184960 582438051232 649777594320
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc22 (x y : ℝ) : 0 ≤ (1285199876960 * x ^ 2 + 2 * 181657092960 * x * y + 157045529824 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1285199876960 157045529824 181657092960
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc23 (x y : ℝ) : 0 ≤ (162952356480 * x ^ 2 + 2 * 20175199200 * x * y + 15567159936 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 162952356480 15567159936 20175199200
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc24 (x y : ℝ) : 0 ≤ (434606482500 * x ^ 2 + 2 * 144110577600 * x * y + 153232839840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 434606482500 153232839840 144110577600
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc25 (x y : ℝ) : 0 ≤ (2228151859070 * x ^ 2 + 2 * 675829074150 * x * y + 681127173334 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2228151859070 681127173334 675829074150
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc26 (x y : ℝ) : 0 ≤ (4701626481360 * x ^ 2 + 2 * 1170867230640 * x * y + 1150379003184 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4701626481360 1150379003184 1170867230640
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc27 (x y : ℝ) : 0 ≤ (4867240036080 * x ^ 2 + 2 * 931550661360 * x * y + 901365550512 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4867240036080 901365550512 931550661360
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc28 (x y : ℝ) : 0 ≤ (2359043231360 * x ^ 2 + 2 * 342760403520 * x * y + 319543978816 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2359043231360 319543978816 342760403520
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc29 (x y : ℝ) : 0 ≤ (403241601120 * x ^ 2 + 2 * 48943634400 * x * y + 40017268704 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 403241601120 40017268704 48943634400
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc30 (x y : ℝ) : 0 ≤ (534168603450 * x ^ 2 + 2 * 163163833200 * x * y + 174955046445 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 534168603450 174955046445 163163833200
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc31 (x y : ℝ) : 0 ≤ (2234666878480 * x ^ 2 + 2 * 596188720800 * x * y + 612161214536 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2234666878480 612161214536 596188720800
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc32 (x y : ℝ) : 0 ≤ (3565138390160 * x ^ 2 + 2 * 748656538560 * x * y + 754394665240 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3565138390160 754394665240 748656538560
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc33 (x y : ℝ) : 0 ≤ (2440955527360 * x ^ 2 + 2 * 382888874880 * x * y + 376316159648 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2440955527360 376316159648 382888874880
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc34 (x y : ℝ) : 0 ≤ (573711566880 * x ^ 2 + 2 * 69883430400 * x * y + 61880575056 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 573711566880 61880575056 69883430400
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc35 (x y : ℝ) : 0 ≤ (410625264960 * x ^ 2 + 2 * 118617056640 * x * y + 125658517536 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 410625264960 125658517536 118617056640
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc36 (x y : ℝ) : 0 ≤ (1320096123200 * x ^ 2 + 2 * 316294829280 * x * y + 323833955584 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1320096123200 323833955584 316294829280
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc37 (x y : ℝ) : 0 ≤ (1418556953600 * x ^ 2 + 2 * 255720792960 * x * y + 256812468352 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1418556953600 256812468352 255720792960
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc38 (x y : ℝ) : 0 ≤ (482191491840 * x ^ 2 + 2 * 63437385600 * x * y + 59972901888 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 482191491840 59972901888 63437385600
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc39 (x y : ℝ) : 0 ≤ (196010735520 * x ^ 2 + 2 * 54080723520 * x * y + 55809442464 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 196010735520 55809442464 54080723520
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc40 (x y : ℝ) : 0 ≤ (431133509760 * x ^ 2 + 2 * 93432902400 * x * y + 93681040512 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 431133509760 93681040512 93432902400
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc41 (x y : ℝ) : 0 ≤ (233942820480 * x ^ 2 + 2 * 36439891200 * x * y + 35320427136 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 233942820480 35320427136 36439891200
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc42 (x y : ℝ) : 0 ≤ (53759715840 * x ^ 2 + 2 * 14139233280 * x * y + 14086900224 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 53759715840 14086900224 14139233280
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc43 (x y : ℝ) : 0 ≤ (60598195200 * x ^ 2 + 2 * 11849932800 * x * y + 11445580800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 60598195200 11445580800 11849932800
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem A_SCU_hc44 (x y : ℝ) : 0 ≤ (6540134400 * x ^ 2 + 2 * 1622937600 * x * y + 1553356800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6540134400 1553356800 1622937600
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem A_SCU_entry11 (z w : ℝ) : 92160 * A11 (1 + w) z 1 =
      4509563160 * ((1 - z - w) ^ 8) +
      37617971480 * (w * (1 - z - w) ^ 7) +
      146560501980 * (w ^ 2 * (1 - z - w) ^ 6) +
      331315496820 * (w ^ 3 * (1 - z - w) ^ 5) +
      455902264600 * (w ^ 4 * (1 - z - w) ^ 4) +
      379173161760 * (w ^ 5 * (1 - z - w) ^ 3) +
      179673110880 * (w ^ 6 * (1 - z - w) ^ 2) +
      41075910080 * (w ^ 7 * (1 - z - w)) +
      2537099520 * (w ^ 8) +
      52679027520 * (z * (1 - z - w) ^ 7) +
      373367667880 * (z * w * (1 - z - w) ^ 6) +
      1191145005080 * (z * w ^ 2 * (1 - z - w) ^ 5) +
      2126124752020 * (z * w ^ 3 * (1 - z - w) ^ 4) +
      2204808746080 * (z * w ^ 4 * (1 - z - w) ^ 3) +
      1280803135040 * (z * w ^ 5 * (1 - z - w) ^ 2) +
      365211583360 * (z * w ^ 6 * (1 - z - w)) +
      33652689600 * (z * w ^ 7) +
      210441454290 * (z ^ 2 * (1 - z - w) ^ 6) +
      1278795485630 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      3365406669920 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      4700562690960 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      3524452184960 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      1285199876960 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      162952356480 * (z ^ 2 * w ^ 6) +
      434606482500 * (z ^ 3 * (1 - z - w) ^ 5) +
      2228151859070 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      4701626481360 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      4867240036080 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      2359043231360 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      403241601120 * (z ^ 3 * w ^ 5) +
      534168603450 * (z ^ 4 * (1 - z - w) ^ 4) +
      2234666878480 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      3565138390160 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      2440955527360 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      573711566880 * (z ^ 4 * w ^ 4) +
      410625264960 * (z ^ 5 * (1 - z - w) ^ 3) +
      1320096123200 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      1418556953600 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      482191491840 * (z ^ 5 * w ^ 3) +
      196010735520 * (z ^ 6 * (1 - z - w) ^ 2) +
      431133509760 * (z ^ 6 * w * (1 - z - w)) +
      233942820480 * (z ^ 6 * w ^ 2) +
      53759715840 * (z ^ 7 * (1 - z - w)) +
      60598195200 * (z ^ 7 * w) +
      6540134400 * (z ^ 8) := by
  simp only [A11, P0, Pk, K1, K2, weight, kappa]
  ring

private theorem A_SCU_entry22 (z w : ℝ) : 92160 * A22 (1 + w) z 1 =
      2849739891 * ((1 - z - w) ^ 8) +
      21571005760 * (w * (1 - z - w) ^ 7) +
      68596421076 * (w ^ 2 * (1 - z - w) ^ 6) +
      118256665572 * (w ^ 3 * (1 - z - w) ^ 5) +
      119430509432 * (w ^ 4 * (1 - z - w) ^ 4) +
      71195690784 * (w ^ 5 * (1 - z - w) ^ 3) +
      23831782752 * (w ^ 6 * (1 - z - w) ^ 2) +
      3911982784 * (w ^ 7 * (1 - z - w)) +
      222426624 * (w ^ 8) +
      23874369804 * (z * (1 - z - w) ^ 7) +
      154066027736 * (z * w * (1 - z - w) ^ 6) +
      409293155608 * (z * w ^ 2 * (1 - z - w) ^ 5) +
      571538732324 * (z * w ^ 3 * (1 - z - w) ^ 4) +
      446225043104 * (z * w ^ 4 * (1 - z - w) ^ 3) +
      191088676672 * (z * w ^ 5 * (1 - z - w) ^ 2) +
      40445269376 * (z * w ^ 6 * (1 - z - w)) +
      3179636160 * (z * w ^ 7) +
      81685041804 * (z ^ 2 * (1 - z - w) ^ 6) +
      443059476646 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      958117102192 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      1037759846544 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      582438051232 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      157045529824 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      15567159936 * (z ^ 2 * w ^ 6) +
      153232839840 * (z ^ 3 * (1 - z - w) ^ 5) +
      681127173334 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      1150379003184 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      901365550512 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      319543978816 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      40017268704 * (z ^ 3 * w ^ 5) +
      174955046445 * (z ^ 4 * (1 - z - w) ^ 4) +
      612161214536 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      754394665240 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      376316159648 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      61880575056 * (z ^ 4 * w ^ 4) +
      125658517536 * (z ^ 5 * (1 - z - w) ^ 3) +
      323833955584 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      256812468352 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      59972901888 * (z ^ 5 * w ^ 3) +
      55809442464 * (z ^ 6 * (1 - z - w) ^ 2) +
      93681040512 * (z ^ 6 * w * (1 - z - w)) +
      35320427136 * (z ^ 6 * w ^ 2) +
      14086900224 * (z ^ 7 * (1 - z - w)) +
      11445580800 * (z ^ 7 * w) +
      1553356800 * (z ^ 8) := by
  simp only [A22, P0, Pk, Pl, K2, weight, kappa]
  ring

private theorem A_SCU_entry12 (z w : ℝ) : 92160 * A12 (1 + w) z 1 =
      3520992240 * ((1 - z - w) ^ 8) +
      28451855430 * (w * (1 - z - w) ^ 7) +
      95012089470 * (w ^ 2 * (1 - z - w) ^ 6) +
      170479080720 * (w ^ 3 * (1 - z - w) ^ 5) +
      178515443880 * (w ^ 4 * (1 - z - w) ^ 4) +
      110060120160 * (w ^ 5 * (1 - z - w) ^ 3) +
      37856028960 * (w ^ 6 * (1 - z - w) ^ 2) +
      6256419840 * (w ^ 7 * (1 - z - w)) +
      342921600 * (w ^ 8) +
      25311712320 * (z * (1 - z - w) ^ 7) +
      174757885650 * (z * w * (1 - z - w) ^ 6) +
      484981146540 * (z * w ^ 2 * (1 - z - w) ^ 5) +
      696933879840 * (z * w ^ 3 * (1 - z - w) ^ 4) +
      555405130080 * (z * w ^ 4 * (1 - z - w) ^ 3) +
      241674700320 * (z * w ^ 5 * (1 - z - w) ^ 2) +
      51921040320 * (z * w ^ 6 * (1 - z - w)) +
      4233427200 * (z * w ^ 7) +
      79790093280 * (z ^ 2 * (1 - z - w) ^ 6) +
      460658243250 * (z ^ 2 * w * (1 - z - w) ^ 5) +
      1031460650910 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 4) +
      1138553971200 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 3) +
      649777594320 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 2) +
      181657092960 * (z ^ 2 * w ^ 5 * (1 - z - w)) +
      20175199200 * (z ^ 2 * w ^ 6) +
      144110577600 * (z ^ 3 * (1 - z - w) ^ 5) +
      675829074150 * (z ^ 3 * w * (1 - z - w) ^ 4) +
      1170867230640 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 3) +
      931550661360 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 2) +
      342760403520 * (z ^ 3 * w ^ 4 * (1 - z - w)) +
      48943634400 * (z ^ 3 * w ^ 5) +
      163163833200 * (z ^ 4 * (1 - z - w) ^ 4) +
      596188720800 * (z ^ 4 * w * (1 - z - w) ^ 3) +
      748656538560 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 2) +
      382888874880 * (z ^ 4 * w ^ 3 * (1 - z - w)) +
      69883430400 * (z ^ 4 * w ^ 4) +
      118617056640 * (z ^ 5 * (1 - z - w) ^ 3) +
      316294829280 * (z ^ 5 * w * (1 - z - w) ^ 2) +
      255720792960 * (z ^ 5 * w ^ 2 * (1 - z - w)) +
      63437385600 * (z ^ 5 * w ^ 3) +
      54080723520 * (z ^ 6 * (1 - z - w) ^ 2) +
      93432902400 * (z ^ 6 * w * (1 - z - w)) +
      36439891200 * (z ^ 6 * w ^ 2) +
      14139233280 * (z ^ 7 * (1 - z - w)) +
      11849932800 * (z ^ 7 * w) +
      1622937600 * (z ^ 8) := by
  simp only [A12, P0, Pk, Pl, K12, weight]
  ring
private def A_SCU_data (z w : ℝ) : List (ℝ × ℝ × ℝ × ℝ) :=
  [(4509563160, 2849739891, 3520992240, (1 - z - w) ^ 8),
  (37617971480, 21571005760, 28451855430, w * (1 - z - w) ^ 7),
  (146560501980, 68596421076, 95012089470, w ^ 2 * (1 - z - w) ^ 6),
  (331315496820, 118256665572, 170479080720, w ^ 3 * (1 - z - w) ^ 5),
  (455902264600, 119430509432, 178515443880, w ^ 4 * (1 - z - w) ^ 4),
  (379173161760, 71195690784, 110060120160, w ^ 5 * (1 - z - w) ^ 3),
  (179673110880, 23831782752, 37856028960, w ^ 6 * (1 - z - w) ^ 2),
  (41075910080, 3911982784, 6256419840, w ^ 7 * (1 - z - w)),
  (2537099520, 222426624, 342921600, w ^ 8),
  (52679027520, 23874369804, 25311712320, z * (1 - z - w) ^ 7),
  (373367667880, 154066027736, 174757885650, z * w * (1 - z - w) ^ 6),
  (1191145005080, 409293155608, 484981146540, z * w ^ 2 * (1 - z - w) ^ 5),
  (2126124752020, 571538732324, 696933879840, z * w ^ 3 * (1 - z - w) ^ 4),
  (2204808746080, 446225043104, 555405130080, z * w ^ 4 * (1 - z - w) ^ 3),
  (1280803135040, 191088676672, 241674700320, z * w ^ 5 * (1 - z - w) ^ 2),
  (365211583360, 40445269376, 51921040320, z * w ^ 6 * (1 - z - w)),
  (33652689600, 3179636160, 4233427200, z * w ^ 7),
  (210441454290, 81685041804, 79790093280, z ^ 2 * (1 - z - w) ^ 6),
  (1278795485630, 443059476646, 460658243250, z ^ 2 * w * (1 - z - w) ^ 5),
  (3365406669920, 958117102192, 1031460650910, z ^ 2 * w ^ 2 * (1 - z - w) ^ 4),
  (4700562690960, 1037759846544, 1138553971200, z ^ 2 * w ^ 3 * (1 - z - w) ^ 3),
  (3524452184960, 582438051232, 649777594320, z ^ 2 * w ^ 4 * (1 - z - w) ^ 2),
  (1285199876960, 157045529824, 181657092960, z ^ 2 * w ^ 5 * (1 - z - w)),
  (162952356480, 15567159936, 20175199200, z ^ 2 * w ^ 6),
  (434606482500, 153232839840, 144110577600, z ^ 3 * (1 - z - w) ^ 5),
  (2228151859070, 681127173334, 675829074150, z ^ 3 * w * (1 - z - w) ^ 4),
  (4701626481360, 1150379003184, 1170867230640, z ^ 3 * w ^ 2 * (1 - z - w) ^ 3),
  (4867240036080, 901365550512, 931550661360, z ^ 3 * w ^ 3 * (1 - z - w) ^ 2),
  (2359043231360, 319543978816, 342760403520, z ^ 3 * w ^ 4 * (1 - z - w)),
  (403241601120, 40017268704, 48943634400, z ^ 3 * w ^ 5),
  (534168603450, 174955046445, 163163833200, z ^ 4 * (1 - z - w) ^ 4),
  (2234666878480, 612161214536, 596188720800, z ^ 4 * w * (1 - z - w) ^ 3),
  (3565138390160, 754394665240, 748656538560, z ^ 4 * w ^ 2 * (1 - z - w) ^ 2),
  (2440955527360, 376316159648, 382888874880, z ^ 4 * w ^ 3 * (1 - z - w)),
  (573711566880, 61880575056, 69883430400, z ^ 4 * w ^ 4),
  (410625264960, 125658517536, 118617056640, z ^ 5 * (1 - z - w) ^ 3),
  (1320096123200, 323833955584, 316294829280, z ^ 5 * w * (1 - z - w) ^ 2),
  (1418556953600, 256812468352, 255720792960, z ^ 5 * w ^ 2 * (1 - z - w)),
  (482191491840, 59972901888, 63437385600, z ^ 5 * w ^ 3),
  (196010735520, 55809442464, 54080723520, z ^ 6 * (1 - z - w) ^ 2),
  (431133509760, 93681040512, 93432902400, z ^ 6 * w * (1 - z - w)),
  (233942820480, 35320427136, 36439891200, z ^ 6 * w ^ 2),
  (53759715840, 14086900224, 14139233280, z ^ 7 * (1 - z - w)),
  (60598195200, 11445580800, 11849932800, z ^ 7 * w),
  (6540134400, 1553356800, 1622937600, z ^ 8)]

private theorem A_SCU_entry11_list (z w : ℝ) :
    92160 * A11 (1 + w) z 1 = ((A_SCU_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [A_SCU_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_SCU_entry11 z w

private theorem A_SCU_entry22_list (z w : ℝ) :
    92160 * A22 (1 + w) z 1 = ((A_SCU_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [A_SCU_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_SCU_entry22 z w

private theorem A_SCU_entry12_list (z w : ℝ) :
    92160 * A12 (1 + w) z 1 = ((A_SCU_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [A_SCU_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using A_SCU_entry12 z w

private theorem A_SCU {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ A11 (1 + w) z 1 * x ^ 2 + 2 * A12 (1 + w) z 1 * x * y + A22 (1 + w) z 1 * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (A_SCU_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (A_SCU_hc0 x y) (by positivity),
      mul_nonneg (A_SCU_hc1 x y) (by positivity),
      mul_nonneg (A_SCU_hc2 x y) (by positivity),
      mul_nonneg (A_SCU_hc3 x y) (by positivity),
      mul_nonneg (A_SCU_hc4 x y) (by positivity),
      mul_nonneg (A_SCU_hc5 x y) (by positivity),
      mul_nonneg (A_SCU_hc6 x y) (by positivity),
      mul_nonneg (A_SCU_hc7 x y) (by positivity),
      mul_nonneg (A_SCU_hc8 x y) (by positivity),
      mul_nonneg (A_SCU_hc9 x y) (by positivity),
      mul_nonneg (A_SCU_hc10 x y) (by positivity),
      mul_nonneg (A_SCU_hc11 x y) (by positivity),
      mul_nonneg (A_SCU_hc12 x y) (by positivity),
      mul_nonneg (A_SCU_hc13 x y) (by positivity),
      mul_nonneg (A_SCU_hc14 x y) (by positivity),
      mul_nonneg (A_SCU_hc15 x y) (by positivity),
      mul_nonneg (A_SCU_hc16 x y) (by positivity),
      mul_nonneg (A_SCU_hc17 x y) (by positivity),
      mul_nonneg (A_SCU_hc18 x y) (by positivity),
      mul_nonneg (A_SCU_hc19 x y) (by positivity),
      mul_nonneg (A_SCU_hc20 x y) (by positivity),
      mul_nonneg (A_SCU_hc21 x y) (by positivity),
      mul_nonneg (A_SCU_hc22 x y) (by positivity),
      mul_nonneg (A_SCU_hc23 x y) (by positivity),
      mul_nonneg (A_SCU_hc24 x y) (by positivity),
      mul_nonneg (A_SCU_hc25 x y) (by positivity),
      mul_nonneg (A_SCU_hc26 x y) (by positivity),
      mul_nonneg (A_SCU_hc27 x y) (by positivity),
      mul_nonneg (A_SCU_hc28 x y) (by positivity),
      mul_nonneg (A_SCU_hc29 x y) (by positivity),
      mul_nonneg (A_SCU_hc30 x y) (by positivity),
      mul_nonneg (A_SCU_hc31 x y) (by positivity),
      mul_nonneg (A_SCU_hc32 x y) (by positivity),
      mul_nonneg (A_SCU_hc33 x y) (by positivity),
      mul_nonneg (A_SCU_hc34 x y) (by positivity),
      mul_nonneg (A_SCU_hc35 x y) (by positivity),
      mul_nonneg (A_SCU_hc36 x y) (by positivity),
      mul_nonneg (A_SCU_hc37 x y) (by positivity),
      mul_nonneg (A_SCU_hc38 x y) (by positivity),
      mul_nonneg (A_SCU_hc39 x y) (by positivity),
      mul_nonneg (A_SCU_hc40 x y) (by positivity),
      mul_nonneg (A_SCU_hc41 x y) (by positivity),
      mul_nonneg (A_SCU_hc42 x y) (by positivity),
      mul_nonneg (A_SCU_hc43 x y) (by positivity),
      mul_nonneg (A_SCU_hc44 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (A_SCU_data z w) x y hcoeff
  rw [← A_SCU_entry11_list, ← A_SCU_entry12_list, ← A_SCU_entry22_list] at hpos
  nlinarith only [hpos]

/-- Equation (21) at the axial spectral value, on the whole closed triangle.
The proof checks the three finite triangle expansions above. -/
theorem axial_matrix_nonneg {v b : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hsum : v + b ≤ 2) (x y : ℝ) :
    0 ≤ A11 v b 1 * x ^ 2 + 2 * A12 v b 1 * x * y + A22 v b 1 * y ^ 2 := by
  by_cases horder : b ≤ v
  · by_cases hv1 : v ≤ 1
    · have h := A_OSC (z := v - b) (w := b) (by linarith) hb (by linarith) x y
      simpa only [sub_add_cancel] using h
    · have h := A_SCU (z := b) (w := v - 1) hb (by linarith) (by linarith) x y
      simpa only [show 1 + (v - 1) = v by ring] using h
  · have h := A_OCW (z := v) (w := (b - v) / 2) hv (by linarith) (by linarith) x y
    simpa only [show v + 2 * ((b - v) / 2) = b by ring] using h

/-- The exact matrix monotonicity identity used to move away from the axial
spectral value. Its remainder is a square and a nonnegative diagonal term. -/
theorem spectral_matrix_identity (v b σ x y : ℝ) :
    A11 v b σ * x ^ 2 + 2 * A12 v b σ * x * y + A22 v b σ * y ^ 2 =
      (A11 v b 1 * x ^ 2 + 2 * A12 v b 1 * x * y + A22 v b 1 * y ^ 2) +
      (1 - σ) * v ^ 2 * ((51 * v * x - Pl v b * y) ^ 2 +
        (51 / 5) * v * P0 v b * y ^ 2) := by
  unfold A11 A12 A22 K1 K2 K12 P0 Pk Pl
  ring

/-- The full matrix inequality (21) for every spectral value `σ ≤ 1`.
The lower bound `-1 ≤ σ` is needed later for the Schur complement, but
is not needed for this monotonicity implication. -/
theorem spectral_matrix_nonneg {v b σ : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hsum : v + b ≤ 2) (hσ : σ ≤ 1) (x y : ℝ) :
    0 ≤ A11 v b σ * x ^ 2 + 2 * A12 v b σ * x * y + A22 v b σ * y ^ 2 := by
  have hbase := axial_matrix_nonneg hv hb hsum x y
  have hd : 0 ≤ 2 - v - b := by linarith
  have hw : 0 ≤ weight v b := sq_nonneg _
  have hp0 : 0 ≤ P0 v b := by unfold P0 Pk; positivity
  rw [spectral_matrix_identity]
  exact add_nonneg hbase (by positivity)

def kappaV (v b : ℝ) : ℝ :=
  (-41) * v ^ 3 +
    (237 / 4) * v ^ 2 * b +
    (879 / 4) * v ^ 2 +
    (101 / 2) * v * b ^ 2 +
    (-128) * v * b +
    (-379) * v +
    (23 / 2) * b ^ 3 +
    (-319 / 4) * b ^ 2 +
    (3461 / 36) * b +
    (2957 / 18)

def kappaB (v b : ℝ) : ℝ :=
  (79 / 4) * v ^ 3 +
    (101 / 2) * v ^ 2 * b +
    (-64) * v ^ 2 +
    (69 / 2) * v * b ^ 2 +
    (-319 / 2) * v * b +
    (3461 / 36) * v +
    61 * b ^ 3 +
    (-1059 / 4) * b ^ 2 +
    364 * b +
    (-4007 / 36)

theorem hasDerivAt_kappa_first (v b : ℝ) :
    HasDerivAt (fun x => kappa x b) (kappaV v b) v := by
  have ha := (hasDerivAt_id v).sub_const 1
  have h := (((((((((((((((ha.pow 4).const_mul ((-41 / 4) * (b - 1) ^ 0)).add ((ha.pow 3).const_mul ((79 / 4) * (b - 1) ^ 1))).add ((ha.pow 3).const_mul (52 * (b - 1) ^ 0))).add ((ha.pow 2).const_mul ((101 / 4) * (b - 1) ^ 2))).add ((ha.pow 2).const_mul ((183 / 4) * (b - 1) ^ 1))).add ((ha.pow 2).const_mul ((-43 / 4) * (b - 1) ^ 0))).add ((ha.pow 1).const_mul ((23 / 2) * (b - 1) ^ 3))).add ((ha.pow 1).const_mul ((21 / 4) * (b - 1) ^ 2))).add ((ha.pow 1).const_mul ((61 / 18) * (b - 1) ^ 1))).add ((ha.pow 1).const_mul ((-79 / 3) * (b - 1) ^ 0))).add ((ha.pow 0).const_mul ((61 / 4) * (b - 1) ^ 4))).add ((ha.pow 0).const_mul ((-63 / 4) * (b - 1) ^ 3))).add ((ha.pow 0).const_mul ((-45 / 4) * (b - 1) ^ 2))).add ((ha.pow 0).const_mul ((79 / 3) * (b - 1) ^ 1)))
  convert h using 1
  · ext x
    unfold kappa
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  · unfold kappaV
    simp only [id_eq]
    ring

theorem hasDerivAt_kappa_second (v b : ℝ) :
    HasDerivAt (fun x => kappa v x) (kappaB v b) b := by
  have ha := (hasDerivAt_id b).sub_const 1
  have h := (((((((((((((((ha.pow 0).const_mul ((-41 / 4) * (v - 1) ^ 4)).add ((ha.pow 1).const_mul ((79 / 4) * (v - 1) ^ 3))).add ((ha.pow 0).const_mul (52 * (v - 1) ^ 3))).add ((ha.pow 2).const_mul ((101 / 4) * (v - 1) ^ 2))).add ((ha.pow 1).const_mul ((183 / 4) * (v - 1) ^ 2))).add ((ha.pow 0).const_mul ((-43 / 4) * (v - 1) ^ 2))).add ((ha.pow 3).const_mul ((23 / 2) * (v - 1) ^ 1))).add ((ha.pow 2).const_mul ((21 / 4) * (v - 1) ^ 1))).add ((ha.pow 1).const_mul ((61 / 18) * (v - 1) ^ 1))).add ((ha.pow 0).const_mul ((-79 / 3) * (v - 1) ^ 1))).add ((ha.pow 4).const_mul ((61 / 4) * (v - 1) ^ 0))).add ((ha.pow 3).const_mul ((-63 / 4) * (v - 1) ^ 0))).add ((ha.pow 2).const_mul ((-45 / 4) * (v - 1) ^ 0))).add ((ha.pow 1).const_mul ((79 / 3) * (v - 1) ^ 0)))
  convert h using 1
  · ext x
    unfold kappa
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  · unfold kappaB
    simp only [id_eq]
    ring

def denominator (v b : ℝ) : ℝ := 4 + v ^ 2 + b ^ 2
def radialDenominator (v : ℝ) : ℝ := 1 + 6 * v + v ^ 2
def axialCoefficient (v b : ℝ) : ℝ :=
  weight v b * (-70 + 100 * v - 25 * v ^ 2 - 5 * b ^ 2) +
    (17 / 6) * (6 * ((v - 1) ^ 2 + (b - 1) ^ 2) + 32 * (v - 1) * (2 - v - b))
def Hdiag (v b : ℝ) : ℝ :=
  8 * v * denominator v b * theta v b * (1 + v) -
    radialDenominator v * (158 * v + denominator v b *
      (v * (axialCoefficient v b + kappaV v b) + 2 * kappa v b / 3))
def Sbound (v b : ℝ) : ℝ :=
  (41 / 5) * v * b + ((5 / 4) * b * (1 - v) ^ 2 + (4 / 5) * v * (1 - b) ^ 2) / 2
def mixedNumerator (v b : ℝ) : ℝ :=
  denominator v b * (kappaB v b + kappaB b v) / 2 - 158
def Hmixed (v b : ℝ) : ℝ := Sbound v b * mixedNumerator v b

private theorem B_OAS_hc0 (x y : ℝ) : 0 ≤ (65413120 * x ^ 2 + 2 * 0 * x * y + 65413120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 65413120 65413120 0
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc1 (x y : ℝ) : 0 ≤ (768942080 * x ^ 2 + 2 * (-133423104) * x * y + 752844800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 768942080 752844800 (-133423104)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc2 (x y : ℝ) : 0 ≤ (3102197760 * x ^ 2 + 2 * (-863834112) * x * y + 3415869440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3102197760 3415869440 (-863834112)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc3 (x y : ℝ) : 0 ≤ (6619097600 * x ^ 2 + 2 * (-2481039360) * x * y + 8497295360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6619097600 8497295360 (-2481039360)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc4 (x y : ℝ) : 0 ≤ (8519705600 * x ^ 2 + 2 * (-4130804736) * x * y + 13078190080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 8519705600 13078190080 (-4130804736)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc5 (x y : ℝ) : 0 ≤ (6914861440 * x ^ 2 + 2 * (-4369367040) * x * y + 13062400000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6914861440 13062400000 (-4369367040)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc6 (x y : ℝ) : 0 ≤ (3543654400 * x ^ 2 + 2 * (-3018777600) * x * y + 8517160960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3543654400 8517160960 (-3018777600)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc7 (x y : ℝ) : 0 ≤ (1123260480 * x ^ 2 + 2 * (-1337256960) * x * y + 3508029440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1123260480 3508029440 (-1337256960)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc8 (x y : ℝ) : 0 ≤ (217338880 * x ^ 2 + 2 * (-348407808) * x * y + 829952000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 217338880 829952000 (-348407808)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc9 (x y : ℝ) : 0 ≤ (24092160 * x ^ 2 + 2 * (-40737792) * x * y + 86016000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 24092160 86016000 (-40737792)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc10 (x y : ℝ) : 0 ≤ (760893440 * x ^ 2 + 2 * (-170948352) * x * y + 760893440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 760893440 760893440 (-170948352)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc11 (x y : ℝ) : 0 ≤ (7266693120 * x ^ 2 + 2 * (-2996311680) * x * y + 7580364800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7266693120 7580364800 (-2996311680)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc12 (x y : ℝ) : 0 ≤ (25423996160 * x ^ 2 + 2 * (-13760692032) * x * y + 29375939840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 25423996160 29375939840 (-13760692032)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc13 (x y : ℝ) : 0 ≤ (47330421760 * x ^ 2 + 2 * (-31098090144) * x * y + 61264896000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 47330421760 61264896000 (-31098090144)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc14 (x y : ℝ) : 0 ≤ (53256127040 * x ^ 2 + 2 * (-41155529856) * x * y + 76993188800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 53256127040 76993188800 (-41155529856)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc15 (x y : ℝ) : 0 ≤ (38162003200 * x ^ 2 + 2 * (-33876050304) * x * y + 60410876160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 38162003200 60410876160 (-33876050304)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc16 (x y : ℝ) : 0 ≤ (17632998560 * x ^ 2 + 2 * (-17334445536) * x * y + 29111903200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 17632998560 29111903200 (-17334445536)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc17 (x y : ℝ) : 0 ≤ (5013623360 * x ^ 2 + 2 * (-5122989312) * x * y + 7919686080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 5013623360 7919686080 (-5122989312)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc18 (x y : ℝ) : 0 ≤ (684373760 * x ^ 2 + 2 * (-671825664) * x * y + 933897760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 684373760 933897760 (-671825664)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc19 (x y : ℝ) : 0 ≤ (3711764480 * x ^ 2 + 2 * (-1619632512) * x * y + 3711764480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3711764480 3711764480 (-1619632512)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc20 (x y : ℝ) : 0 ≤ (28774671360 * x ^ 2 + 2 * (-17221631040) * x * y + 30750643200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 28774671360 30750643200 (-17221631040)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc21 (x y : ℝ) : 0 ≤ (84574977280 * x ^ 2 + 2 * (-60810326976) * x * y + 98638961920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 84574977280 98638961920 (-60810326976)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc22 (x y : ℝ) : 0 ≤ (131648405760 * x ^ 2 + 2 * (-108187004544) * x * y + 166572573120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 131648405760 166572573120 (-108187004544)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc23 (x y : ℝ) : 0 ≤ (121899264640 * x ^ 2 + 2 * (-110478091632) * x * y + 163288773760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 121899264640 163288773760 (-110478091632)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc24 (x y : ℝ) : 0 ≤ (69674734240 * x ^ 2 + 2 * (-66707564592) * x * y + 94041361600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 69674734240 94041361600 (-66707564592)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc25 (x y : ℝ) : 0 ≤ (23585061280 * x ^ 2 + 2 * (-22531986528) * x * y + 29730955360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 23585061280 29730955360 (-22531986528)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc26 (x y : ℝ) : 0 ≤ (3680782480 * x ^ 2 + 2 * (-3316860672) * x * y + 4005877600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3680782480 4005877600 (-3316860672)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc27 (x y : ℝ) : 0 ≤ (9920885760 * x ^ 2 + 2 * (-5965350432) * x * y + 9920885760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 9920885760 9920885760 (-5965350432)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc28 (x y : ℝ) : 0 ≤ (62114142720 * x ^ 2 + 2 * (-45728303280) * x * y + 66802137600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 62114142720 66802137600 (-45728303280)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc29 (x y : ℝ) : 0 ≤ (148853092640 * x ^ 2 + 2 * (-124803813792) * x * y + 171908729120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 148853092640 171908729120 (-124803813792)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc30 (x y : ℝ) : 0 ≤ (185333807360 * x ^ 2 + 2 * (-169623069600) * x * y + 224924409600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 185333807360 224924409600 (-169623069600)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc31 (x y : ℝ) : 0 ≤ (131851537360 * x ^ 2 + 2 * (-126020279448) * x * y + 160844009040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 131851537360 160844009040 (-126020279448)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc32 (x y : ℝ) : 0 ≤ (52794631200 * x ^ 2 + 2 * (-49875604560) * x * y + 60413316320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 52794631200 60413316320 (-49875604560)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc33 (x y : ℝ) : 0 ≤ (9442244840 * x ^ 2 + 2 * (-8358032376) * x * y + 9412328520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 9442244840 9412328520 (-8358032376)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc34 (x y : ℝ) : 0 ≤ (16114535040 * x ^ 2 + 2 * (-11694054768) * x * y + 16114535040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 16114535040 16114535040 (-11694054768)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc35 (x y : ℝ) : 0 ≤ (80126106240 * x ^ 2 + 2 * (-66996501024) * x * y + 85890015360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 80126106240 85890015360 (-66996501024)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc36 (x y : ℝ) : 0 ≤ (150582376320 * x ^ 2 + 2 * (-137797344648) * x * y + 169927950720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 150582376320 169927950720 (-137797344648)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc37 (x y : ℝ) : 0 ≤ (140922909840 * x ^ 2 + 2 * (-134975315424) * x * y + 161127648560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 140922909840 161127648560 (-134975315424)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc38 (x y : ℝ) : 0 ≤ (68626882640 * x ^ 2 + 2 * (-65202397092) * x * y + 74660334640 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 68626882640 74660334640 (-65202397092)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc39 (x y : ℝ) : 0 ≤ (14292149040 * x ^ 2 + 2 * (-12738598764) * x * y + 13739270960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 14292149040 13739270960 (-12738598764)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc40 (x y : ℝ) : 0 ≤ (16601612160 * x ^ 2 + 2 * (-13598342736) * x * y + 16601612160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 16601612160 16601612160 (-13598342736)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc41 (x y : ℝ) : 0 ≤ (63449174400 * x ^ 2 + 2 * (-57493812240) * x * y + 67318289280 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 63449174400 67318289280 (-57493812240)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc42 (x y : ℝ) : 0 ≤ (88047030880 * x ^ 2 + 2 * (-84254117448) * x * y + 95821003360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 88047030880 95821003360 (-84254117448)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc43 (x y : ℝ) : 0 ≤ (55390166960 * x ^ 2 + 2 * (-53157515286) * x * y + 58452769040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 55390166960 58452769040 (-53157515286)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc44 (x y : ℝ) : 0 ≤ (13862722720 * x ^ 2 + 2 * (-12586076178) * x * y + 13174861240 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 13862722720 13174861240 (-12586076178)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc45 (x y : ℝ) : 0 ≤ (10897288640 * x ^ 2 + 2 * (-9680731728) * x * y + 10897288640 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 10897288640 10897288640 (-9680731728)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc46 (x y : ℝ) : 0 ≤ (30216649600 * x ^ 2 + 2 * (-28722051948) * x * y + 31512311680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 30216649600 31512311680 (-28722051948)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc47 (x y : ℝ) : 0 ≤ (27711182480 * x ^ 2 + 2 * (-26818681746) * x * y + 28639138320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 27711182480 28639138320 (-26818681746)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc48 (x y : ℝ) : 0 ≤ (8843240540 * x ^ 2 + 2 * (-8217437028) * x * y + 8428078560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 8843240540 8428078560 (-8217437028)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc49 (x y : ℝ) : 0 ≤ (4409211520 * x ^ 2 + 2 * (-4133675514) * x * y + 4409211520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4409211520 4409211520 (-4133675514)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc50 (x y : ℝ) : 0 ≤ (7942967040 * x ^ 2 + 2 * (-7715144847) * x * y + 8075532160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7942967040 8075532160 (-7715144847)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc51 (x y : ℝ) : 0 ≤ (3639372850 * x ^ 2 + 2 * (-3461048223) * x * y + 3510579250 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3639372850 3510579250 (-3461048223)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc52 (x y : ℝ) : 0 ≤ (1001156200 * x ^ 2 + 2 * (-969780831) * x * y + 1001156200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1001156200 1001156200 (-969780831)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc53 (x y : ℝ) : 0 ≤ (886041000 * x ^ 2 + 2 * (-859230990) * x * y + 869941800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 886041000 869941800 (-859230990)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_OAS_hc54 (x y : ℝ) : 0 ≤ (97554600 * x ^ 2 + 2 * (-95882805) * x * y + 97554600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 97554600 97554600 (-95882805)
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem B_OAS_entry11 (z w : ℝ) : 552960 * Hdiag (z / 2 + w) (z / 2) =
      65413120 * ((1 - z - w) ^ 9) +
      768942080 * (w * (1 - z - w) ^ 8) +
      3102197760 * (w ^ 2 * (1 - z - w) ^ 7) +
      6619097600 * (w ^ 3 * (1 - z - w) ^ 6) +
      8519705600 * (w ^ 4 * (1 - z - w) ^ 5) +
      6914861440 * (w ^ 5 * (1 - z - w) ^ 4) +
      3543654400 * (w ^ 6 * (1 - z - w) ^ 3) +
      1123260480 * (w ^ 7 * (1 - z - w) ^ 2) +
      217338880 * (w ^ 8 * (1 - z - w)) +
      24092160 * (w ^ 9) +
      760893440 * (z * (1 - z - w) ^ 8) +
      7266693120 * (z * w * (1 - z - w) ^ 7) +
      25423996160 * (z * w ^ 2 * (1 - z - w) ^ 6) +
      47330421760 * (z * w ^ 3 * (1 - z - w) ^ 5) +
      53256127040 * (z * w ^ 4 * (1 - z - w) ^ 4) +
      38162003200 * (z * w ^ 5 * (1 - z - w) ^ 3) +
      17632998560 * (z * w ^ 6 * (1 - z - w) ^ 2) +
      5013623360 * (z * w ^ 7 * (1 - z - w)) +
      684373760 * (z * w ^ 8) +
      3711764480 * (z ^ 2 * (1 - z - w) ^ 7) +
      28774671360 * (z ^ 2 * w * (1 - z - w) ^ 6) +
      84574977280 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      131648405760 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      121899264640 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      69674734240 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      23585061280 * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      3680782480 * (z ^ 2 * w ^ 7) +
      9920885760 * (z ^ 3 * (1 - z - w) ^ 6) +
      62114142720 * (z ^ 3 * w * (1 - z - w) ^ 5) +
      148853092640 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      185333807360 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      131851537360 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      52794631200 * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      9442244840 * (z ^ 3 * w ^ 6) +
      16114535040 * (z ^ 4 * (1 - z - w) ^ 5) +
      80126106240 * (z ^ 4 * w * (1 - z - w) ^ 4) +
      150582376320 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      140922909840 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      68626882640 * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      14292149040 * (z ^ 4 * w ^ 5) +
      16601612160 * (z ^ 5 * (1 - z - w) ^ 4) +
      63449174400 * (z ^ 5 * w * (1 - z - w) ^ 3) +
      88047030880 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      55390166960 * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      13862722720 * (z ^ 5 * w ^ 4) +
      10897288640 * (z ^ 6 * (1 - z - w) ^ 3) +
      30216649600 * (z ^ 6 * w * (1 - z - w) ^ 2) +
      27711182480 * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      8843240540 * (z ^ 6 * w ^ 3) +
      4409211520 * (z ^ 7 * (1 - z - w) ^ 2) +
      7942967040 * (z ^ 7 * w * (1 - z - w)) +
      3639372850 * (z ^ 7 * w ^ 2) +
      1001156200 * (z ^ 8 * (1 - z - w)) +
      886041000 * (z ^ 8 * w) +
      97554600 * (z ^ 9) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_OAS_entry22 (z w : ℝ) : 552960 * Hdiag (z / 2) (z / 2 + w) =
      65413120 * ((1 - z - w) ^ 9) +
      752844800 * (w * (1 - z - w) ^ 8) +
      3415869440 * (w ^ 2 * (1 - z - w) ^ 7) +
      8497295360 * (w ^ 3 * (1 - z - w) ^ 6) +
      13078190080 * (w ^ 4 * (1 - z - w) ^ 5) +
      13062400000 * (w ^ 5 * (1 - z - w) ^ 4) +
      8517160960 * (w ^ 6 * (1 - z - w) ^ 3) +
      3508029440 * (w ^ 7 * (1 - z - w) ^ 2) +
      829952000 * (w ^ 8 * (1 - z - w)) +
      86016000 * (w ^ 9) +
      760893440 * (z * (1 - z - w) ^ 8) +
      7580364800 * (z * w * (1 - z - w) ^ 7) +
      29375939840 * (z * w ^ 2 * (1 - z - w) ^ 6) +
      61264896000 * (z * w ^ 3 * (1 - z - w) ^ 5) +
      76993188800 * (z * w ^ 4 * (1 - z - w) ^ 4) +
      60410876160 * (z * w ^ 5 * (1 - z - w) ^ 3) +
      29111903200 * (z * w ^ 6 * (1 - z - w) ^ 2) +
      7919686080 * (z * w ^ 7 * (1 - z - w)) +
      933897760 * (z * w ^ 8) +
      3711764480 * (z ^ 2 * (1 - z - w) ^ 7) +
      30750643200 * (z ^ 2 * w * (1 - z - w) ^ 6) +
      98638961920 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      166572573120 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      163288773760 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      94041361600 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      29730955360 * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      4005877600 * (z ^ 2 * w ^ 7) +
      9920885760 * (z ^ 3 * (1 - z - w) ^ 6) +
      66802137600 * (z ^ 3 * w * (1 - z - w) ^ 5) +
      171908729120 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      224924409600 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      160844009040 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      60413316320 * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      9412328520 * (z ^ 3 * w ^ 6) +
      16114535040 * (z ^ 4 * (1 - z - w) ^ 5) +
      85890015360 * (z ^ 4 * w * (1 - z - w) ^ 4) +
      169927950720 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      161127648560 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      74660334640 * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      13739270960 * (z ^ 4 * w ^ 5) +
      16601612160 * (z ^ 5 * (1 - z - w) ^ 4) +
      67318289280 * (z ^ 5 * w * (1 - z - w) ^ 3) +
      95821003360 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      58452769040 * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      13174861240 * (z ^ 5 * w ^ 4) +
      10897288640 * (z ^ 6 * (1 - z - w) ^ 3) +
      31512311680 * (z ^ 6 * w * (1 - z - w) ^ 2) +
      28639138320 * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      8428078560 * (z ^ 6 * w ^ 3) +
      4409211520 * (z ^ 7 * (1 - z - w) ^ 2) +
      8075532160 * (z ^ 7 * w * (1 - z - w)) +
      3510579250 * (z ^ 7 * w ^ 2) +
      1001156200 * (z ^ 8 * (1 - z - w)) +
      869941800 * (z ^ 8 * w) +
      97554600 * (z ^ 9) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_OAS_entry12 (z w : ℝ) : 552960 * Hmixed (z / 2 + w) (z / 2) =
      (-133423104) * (w * (1 - z - w) ^ 8) +
      (-863834112) * (w ^ 2 * (1 - z - w) ^ 7) +
      (-2481039360) * (w ^ 3 * (1 - z - w) ^ 6) +
      (-4130804736) * (w ^ 4 * (1 - z - w) ^ 5) +
      (-4369367040) * (w ^ 5 * (1 - z - w) ^ 4) +
      (-3018777600) * (w ^ 6 * (1 - z - w) ^ 3) +
      (-1337256960) * (w ^ 7 * (1 - z - w) ^ 2) +
      (-348407808) * (w ^ 8 * (1 - z - w)) +
      (-40737792) * (w ^ 9) +
      (-170948352) * (z * (1 - z - w) ^ 8) +
      (-2996311680) * (z * w * (1 - z - w) ^ 7) +
      (-13760692032) * (z * w ^ 2 * (1 - z - w) ^ 6) +
      (-31098090144) * (z * w ^ 3 * (1 - z - w) ^ 5) +
      (-41155529856) * (z * w ^ 4 * (1 - z - w) ^ 4) +
      (-33876050304) * (z * w ^ 5 * (1 - z - w) ^ 3) +
      (-17334445536) * (z * w ^ 6 * (1 - z - w) ^ 2) +
      (-5122989312) * (z * w ^ 7 * (1 - z - w)) +
      (-671825664) * (z * w ^ 8) +
      (-1619632512) * (z ^ 2 * (1 - z - w) ^ 7) +
      (-17221631040) * (z ^ 2 * w * (1 - z - w) ^ 6) +
      (-60810326976) * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      (-108187004544) * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      (-110478091632) * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      (-66707564592) * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      (-22531986528) * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      (-3316860672) * (z ^ 2 * w ^ 7) +
      (-5965350432) * (z ^ 3 * (1 - z - w) ^ 6) +
      (-45728303280) * (z ^ 3 * w * (1 - z - w) ^ 5) +
      (-124803813792) * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      (-169623069600) * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      (-126020279448) * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      (-49875604560) * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      (-8358032376) * (z ^ 3 * w ^ 6) +
      (-11694054768) * (z ^ 4 * (1 - z - w) ^ 5) +
      (-66996501024) * (z ^ 4 * w * (1 - z - w) ^ 4) +
      (-137797344648) * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      (-134975315424) * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      (-65202397092) * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      (-12738598764) * (z ^ 4 * w ^ 5) +
      (-13598342736) * (z ^ 5 * (1 - z - w) ^ 4) +
      (-57493812240) * (z ^ 5 * w * (1 - z - w) ^ 3) +
      (-84254117448) * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      (-53157515286) * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      (-12586076178) * (z ^ 5 * w ^ 4) +
      (-9680731728) * (z ^ 6 * (1 - z - w) ^ 3) +
      (-28722051948) * (z ^ 6 * w * (1 - z - w) ^ 2) +
      (-26818681746) * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      (-8217437028) * (z ^ 6 * w ^ 3) +
      (-4133675514) * (z ^ 7 * (1 - z - w) ^ 2) +
      (-7715144847) * (z ^ 7 * w * (1 - z - w)) +
      (-3461048223) * (z ^ 7 * w ^ 2) +
      (-969780831) * (z ^ 8 * (1 - z - w)) +
      (-859230990) * (z ^ 8 * w) +
      (-95882805) * (z ^ 9) := by
  simp only [Hmixed, mixedNumerator, Sbound, denominator, kappaB]
  ring
private def B_OAS_data (z w : ℝ) : List (ℝ × ℝ × ℝ × ℝ) :=
  [(65413120, 65413120, 0, (1 - z - w) ^ 9),
  (768942080, 752844800, (-133423104), w * (1 - z - w) ^ 8),
  (3102197760, 3415869440, (-863834112), w ^ 2 * (1 - z - w) ^ 7),
  (6619097600, 8497295360, (-2481039360), w ^ 3 * (1 - z - w) ^ 6),
  (8519705600, 13078190080, (-4130804736), w ^ 4 * (1 - z - w) ^ 5),
  (6914861440, 13062400000, (-4369367040), w ^ 5 * (1 - z - w) ^ 4),
  (3543654400, 8517160960, (-3018777600), w ^ 6 * (1 - z - w) ^ 3),
  (1123260480, 3508029440, (-1337256960), w ^ 7 * (1 - z - w) ^ 2),
  (217338880, 829952000, (-348407808), w ^ 8 * (1 - z - w)),
  (24092160, 86016000, (-40737792), w ^ 9),
  (760893440, 760893440, (-170948352), z * (1 - z - w) ^ 8),
  (7266693120, 7580364800, (-2996311680), z * w * (1 - z - w) ^ 7),
  (25423996160, 29375939840, (-13760692032), z * w ^ 2 * (1 - z - w) ^ 6),
  (47330421760, 61264896000, (-31098090144), z * w ^ 3 * (1 - z - w) ^ 5),
  (53256127040, 76993188800, (-41155529856), z * w ^ 4 * (1 - z - w) ^ 4),
  (38162003200, 60410876160, (-33876050304), z * w ^ 5 * (1 - z - w) ^ 3),
  (17632998560, 29111903200, (-17334445536), z * w ^ 6 * (1 - z - w) ^ 2),
  (5013623360, 7919686080, (-5122989312), z * w ^ 7 * (1 - z - w)),
  (684373760, 933897760, (-671825664), z * w ^ 8),
  (3711764480, 3711764480, (-1619632512), z ^ 2 * (1 - z - w) ^ 7),
  (28774671360, 30750643200, (-17221631040), z ^ 2 * w * (1 - z - w) ^ 6),
  (84574977280, 98638961920, (-60810326976), z ^ 2 * w ^ 2 * (1 - z - w) ^ 5),
  (131648405760, 166572573120, (-108187004544), z ^ 2 * w ^ 3 * (1 - z - w) ^ 4),
  (121899264640, 163288773760, (-110478091632), z ^ 2 * w ^ 4 * (1 - z - w) ^ 3),
  (69674734240, 94041361600, (-66707564592), z ^ 2 * w ^ 5 * (1 - z - w) ^ 2),
  (23585061280, 29730955360, (-22531986528), z ^ 2 * w ^ 6 * (1 - z - w)),
  (3680782480, 4005877600, (-3316860672), z ^ 2 * w ^ 7),
  (9920885760, 9920885760, (-5965350432), z ^ 3 * (1 - z - w) ^ 6),
  (62114142720, 66802137600, (-45728303280), z ^ 3 * w * (1 - z - w) ^ 5),
  (148853092640, 171908729120, (-124803813792), z ^ 3 * w ^ 2 * (1 - z - w) ^ 4),
  (185333807360, 224924409600, (-169623069600), z ^ 3 * w ^ 3 * (1 - z - w) ^ 3),
  (131851537360, 160844009040, (-126020279448), z ^ 3 * w ^ 4 * (1 - z - w) ^ 2),
  (52794631200, 60413316320, (-49875604560), z ^ 3 * w ^ 5 * (1 - z - w)),
  (9442244840, 9412328520, (-8358032376), z ^ 3 * w ^ 6),
  (16114535040, 16114535040, (-11694054768), z ^ 4 * (1 - z - w) ^ 5),
  (80126106240, 85890015360, (-66996501024), z ^ 4 * w * (1 - z - w) ^ 4),
  (150582376320, 169927950720, (-137797344648), z ^ 4 * w ^ 2 * (1 - z - w) ^ 3),
  (140922909840, 161127648560, (-134975315424), z ^ 4 * w ^ 3 * (1 - z - w) ^ 2),
  (68626882640, 74660334640, (-65202397092), z ^ 4 * w ^ 4 * (1 - z - w)),
  (14292149040, 13739270960, (-12738598764), z ^ 4 * w ^ 5),
  (16601612160, 16601612160, (-13598342736), z ^ 5 * (1 - z - w) ^ 4),
  (63449174400, 67318289280, (-57493812240), z ^ 5 * w * (1 - z - w) ^ 3),
  (88047030880, 95821003360, (-84254117448), z ^ 5 * w ^ 2 * (1 - z - w) ^ 2),
  (55390166960, 58452769040, (-53157515286), z ^ 5 * w ^ 3 * (1 - z - w)),
  (13862722720, 13174861240, (-12586076178), z ^ 5 * w ^ 4),
  (10897288640, 10897288640, (-9680731728), z ^ 6 * (1 - z - w) ^ 3),
  (30216649600, 31512311680, (-28722051948), z ^ 6 * w * (1 - z - w) ^ 2),
  (27711182480, 28639138320, (-26818681746), z ^ 6 * w ^ 2 * (1 - z - w)),
  (8843240540, 8428078560, (-8217437028), z ^ 6 * w ^ 3),
  (4409211520, 4409211520, (-4133675514), z ^ 7 * (1 - z - w) ^ 2),
  (7942967040, 8075532160, (-7715144847), z ^ 7 * w * (1 - z - w)),
  (3639372850, 3510579250, (-3461048223), z ^ 7 * w ^ 2),
  (1001156200, 1001156200, (-969780831), z ^ 8 * (1 - z - w)),
  (886041000, 869941800, (-859230990), z ^ 8 * w),
  (97554600, 97554600, (-95882805), z ^ 9)]

private theorem B_OAS_entry11_list (z w : ℝ) :
    552960 * Hdiag (z / 2 + w) (z / 2) = ((B_OAS_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [B_OAS_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_OAS_entry11 z w

private theorem B_OAS_entry22_list (z w : ℝ) :
    552960 * Hdiag (z / 2) (z / 2 + w) = ((B_OAS_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [B_OAS_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_OAS_entry22 z w

private theorem B_OAS_entry12_list (z w : ℝ) :
    552960 * Hmixed (z / 2 + w) (z / 2) = ((B_OAS_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [B_OAS_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_OAS_entry12 z w

private theorem B_OAS {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ Hdiag (z / 2 + w) (z / 2) * x ^ 2 + 2 * Hmixed (z / 2 + w) (z / 2) * x * y + Hdiag (z / 2) (z / 2 + w) * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (B_OAS_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (B_OAS_hc0 x y) (by positivity),
      mul_nonneg (B_OAS_hc1 x y) (by positivity),
      mul_nonneg (B_OAS_hc2 x y) (by positivity),
      mul_nonneg (B_OAS_hc3 x y) (by positivity),
      mul_nonneg (B_OAS_hc4 x y) (by positivity),
      mul_nonneg (B_OAS_hc5 x y) (by positivity),
      mul_nonneg (B_OAS_hc6 x y) (by positivity),
      mul_nonneg (B_OAS_hc7 x y) (by positivity),
      mul_nonneg (B_OAS_hc8 x y) (by positivity),
      mul_nonneg (B_OAS_hc9 x y) (by positivity),
      mul_nonneg (B_OAS_hc10 x y) (by positivity),
      mul_nonneg (B_OAS_hc11 x y) (by positivity),
      mul_nonneg (B_OAS_hc12 x y) (by positivity),
      mul_nonneg (B_OAS_hc13 x y) (by positivity),
      mul_nonneg (B_OAS_hc14 x y) (by positivity),
      mul_nonneg (B_OAS_hc15 x y) (by positivity),
      mul_nonneg (B_OAS_hc16 x y) (by positivity),
      mul_nonneg (B_OAS_hc17 x y) (by positivity),
      mul_nonneg (B_OAS_hc18 x y) (by positivity),
      mul_nonneg (B_OAS_hc19 x y) (by positivity),
      mul_nonneg (B_OAS_hc20 x y) (by positivity),
      mul_nonneg (B_OAS_hc21 x y) (by positivity),
      mul_nonneg (B_OAS_hc22 x y) (by positivity),
      mul_nonneg (B_OAS_hc23 x y) (by positivity),
      mul_nonneg (B_OAS_hc24 x y) (by positivity),
      mul_nonneg (B_OAS_hc25 x y) (by positivity),
      mul_nonneg (B_OAS_hc26 x y) (by positivity),
      mul_nonneg (B_OAS_hc27 x y) (by positivity),
      mul_nonneg (B_OAS_hc28 x y) (by positivity),
      mul_nonneg (B_OAS_hc29 x y) (by positivity),
      mul_nonneg (B_OAS_hc30 x y) (by positivity),
      mul_nonneg (B_OAS_hc31 x y) (by positivity),
      mul_nonneg (B_OAS_hc32 x y) (by positivity),
      mul_nonneg (B_OAS_hc33 x y) (by positivity),
      mul_nonneg (B_OAS_hc34 x y) (by positivity),
      mul_nonneg (B_OAS_hc35 x y) (by positivity),
      mul_nonneg (B_OAS_hc36 x y) (by positivity),
      mul_nonneg (B_OAS_hc37 x y) (by positivity),
      mul_nonneg (B_OAS_hc38 x y) (by positivity),
      mul_nonneg (B_OAS_hc39 x y) (by positivity),
      mul_nonneg (B_OAS_hc40 x y) (by positivity),
      mul_nonneg (B_OAS_hc41 x y) (by positivity),
      mul_nonneg (B_OAS_hc42 x y) (by positivity),
      mul_nonneg (B_OAS_hc43 x y) (by positivity),
      mul_nonneg (B_OAS_hc44 x y) (by positivity),
      mul_nonneg (B_OAS_hc45 x y) (by positivity),
      mul_nonneg (B_OAS_hc46 x y) (by positivity),
      mul_nonneg (B_OAS_hc47 x y) (by positivity),
      mul_nonneg (B_OAS_hc48 x y) (by positivity),
      mul_nonneg (B_OAS_hc49 x y) (by positivity),
      mul_nonneg (B_OAS_hc50 x y) (by positivity),
      mul_nonneg (B_OAS_hc51 x y) (by positivity),
      mul_nonneg (B_OAS_hc52 x y) (by positivity),
      mul_nonneg (B_OAS_hc53 x y) (by positivity),
      mul_nonneg (B_OAS_hc54 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (B_OAS_data z w) x y hcoeff
  rw [← B_OAS_entry11_list, ← B_OAS_entry12_list, ← B_OAS_entry22_list] at hpos
  nlinarith only [hpos]

private theorem B_ASE_hc0 (x y : ℝ) : 0 ≤ (801184320 * x ^ 2 + 2 * (-411481728) * x * y + 268058655 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 801184320 268058655 (-411481728)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc1 (x y : ℝ) : 0 ≤ (8214628800 * x ^ 2 + 2 * (-4609025856) * x * y + 3173049120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 8214628800 3173049120 (-4609025856)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc2 (x y : ℝ) : 0 ≤ (36441336000 * x ^ 2 + 2 * (-22148058240) * x * y + 16173052200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 36441336000 16173052200 (-22148058240)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc3 (x y : ℝ) : 0 ≤ (91489281600 * x ^ 2 + 2 * (-59794467648) * x * y + 46429159680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 91489281600 46429159680 (-59794467648)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc4 (x y : ℝ) : 0 ≤ (142481379840 * x ^ 2 + 2 * (-99599797632) * x * y + 82527394560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 142481379840 82527394560 (-99599797632)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc5 (x y : ℝ) : 0 ≤ (141421989120 * x ^ 2 + 2 * (-105489283584) * x * y + 93954693120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 141421989120 93954693120 (-105489283584)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc6 (x y : ℝ) : 0 ≤ (87917245440 * x ^ 2 + 2 * (-70186266624) * x * y + 68211588480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 87917245440 68211588480 (-70186266624)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc7 (x y : ℝ) : 0 ≤ (31795461120 * x ^ 2 + 2 * (-27574459392) * x * y + 30182983680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 31795461120 30182983680 (-27574459392)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc8 (x y : ℝ) : 0 ≤ (5472952320 * x ^ 2 + 2 * (-5447534592) * x * y + 7247950080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 5472952320 7247950080 (-5447534592)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc9 (x y : ℝ) : 0 ≤ (192737280 * x ^ 2 + 2 * (-325902336) * x * y + 688128000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 192737280 688128000 (-325902336)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc10 (x y : ℝ) : 0 ≤ (6659768160 * x ^ 2 + 2 * (-3774480192) * x * y + 2668414545 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6659768160 2668414545 (-3774480192)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc11 (x y : ℝ) : 0 ≤ (60646594240 * x ^ 2 + 2 * (-37331662752) * x * y + 27635018260 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 60646594240 27635018260 (-37331662752)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc12 (x y : ℝ) : 0 ≤ (235423411680 * x ^ 2 + 2 * (-155814545568) * x * y + 121565829680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 235423411680 121565829680 (-155814545568)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc13 (x y : ℝ) : 0 ≤ (507118147840 * x ^ 2 + 2 * (-357917622720) * x * y + 295612856080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 507118147840 295612856080 (-357917622720)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc14 (x y : ℝ) : 0 ≤ (659659999360 * x ^ 2 + 2 * (-493466728320) * x * y + 433564336480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 659659999360 433564336480 (-493466728320)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc15 (x y : ℝ) : 0 ≤ (526172846080 * x ^ 2 + 2 * (-415755199488) * x * y + 391746174400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 526172846080 391746174400 (-415755199488)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc16 (x y : ℝ) : 0 ≤ (247457405440 * x ^ 2 + 2 * (-206650360320) * x * y + 212023863040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 247457405440 212023863040 (-206650360320)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc17 (x y : ℝ) : 0 ≤ (60737986560 * x ^ 2 + 2 * (-54076234752) * x * y + 62300025600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 60737986560 62300025600 (-54076234752)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc18 (x y : ℝ) : 0 ≤ (5474990080 * x ^ 2 + 2 * (-5374605312) * x * y + 7471182080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 5474990080 7471182080 (-5374605312)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc19 (x y : ℝ) : 0 ≤ (24731126870 * x ^ 2 + 2 * (-15706834722) * x * y + 12111070085 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 24731126870 12111070085 (-15706834722)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc20 (x y : ℝ) : 0 ≤ (197409465390 * x ^ 2 + 2 * (-134329715382) * x * y + 106918811160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 197409465390 106918811160 (-134329715382)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc21 (x y : ℝ) : 0 ≤ (657946610000 * x ^ 2 + 2 * (-475149772500) * x * y + 394891295780 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 657946610000 394891295780 (-475149772500)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc22 (x y : ℝ) : 0 ≤ (1183535463800 * x ^ 2 + 2 * (-900172885536) * x * y + 787188651920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1183535463800 787188651920 (-900172885536)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc23 (x y : ℝ) : 0 ≤ (1235628716960 * x ^ 2 + 2 * (-983906926368) * x * y + 911786934320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1235628716960 911786934320 (-983906926368)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc24 (x y : ℝ) : 0 ≤ (743250805280 * x ^ 2 + 2 * (-617063256096) * x * y + 611770981760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 743250805280 611770981760 (-617063256096)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc25 (x y : ℝ) : 0 ≤ (235335540480 * x ^ 2 + 2 * (-203336929728) * x * y + 219136635840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 235335540480 219136635840 (-203336929728)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc26 (x y : ℝ) : 0 ≤ (29446259840 * x ^ 2 + 2 * (-26534885376) * x * y + 32047020800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 29446259840 32047020800 (-26534885376)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc27 (x y : ℝ) : 0 ≤ (54548120435 * x ^ 2 + 2 * (-38984838126) * x * y + 32521501695 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 54548120435 32521501695 (-38984838126)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc28 (x y : ℝ) : 0 ≤ (373454270660 * x ^ 2 + 2 * (-280638182172) * x * y + 238451526660 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 373454270660 238451526660 (-280638182172)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc29 (x y : ℝ) : 0 ≤ (1037775174300 * x ^ 2 + 2 * (-814280610348) * x * y + 715975698860 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1037775174300 715975698860 (-814280610348)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc30 (x y : ℝ) : 0 ≤ (1495013327520 * x ^ 2 + 2 * (-1217537869200) * x * y + 1119956796960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1495013327520 1119956796960 (-1217537869200)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc31 (x y : ℝ) : 0 ≤ (1173383726480 * x ^ 2 + 2 * (-986761126464) * x * y + 958489932240 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1173383726480 958489932240 (-986761126464)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc32 (x y : ℝ) : 0 ≤ (472784120640 * x ^ 2 + 2 * (-408725519232) * x * y + 423899289920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 472784120640 423899289920 (-408725519232)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc33 (x y : ℝ) : 0 ≤ (75537958720 * x ^ 2 + 2 * (-66864259008) * x * y + 75298628160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 75537958720 75298628160 (-66864259008)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc34 (x y : ℝ) : 0 ≤ (79451682980 * x ^ 2 + 2 * (-63339743556) * x * y + 56332131420 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 79451682980 56332131420 (-63339743556)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc35 (x y : ℝ) : 0 ≤ (451880195880 * x ^ 2 + 2 * (-371289053736) * x * y + 333163531520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 451880195880 333163531520 (-371289053736)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc36 (x y : ℝ) : 0 ≤ (1002011957360 * x ^ 2 + 2 * (-845391756012) * x * y + 779672365120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1002011957360 779672365120 (-845391756012)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc37 (x y : ℝ) : 0 ≤ (1081077082560 * x ^ 2 + 2 * (-932931661272) * x * y + 896060984800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1081077082560 896060984800 (-932931661272)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc38 (x y : ℝ) : 0 ≤ (565844359040 * x ^ 2 + 2 * (-497405434032) * x * y + 503138530240 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 565844359040 503138530240 (-497405434032)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc39 (x y : ℝ) : 0 ≤ (114337192320 * x ^ 2 + 2 * (-101908790112) * x * y + 109914167680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 114337192320 109914167680 (-101908790112)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc40 (x y : ℝ) : 0 ≤ (79529686180 * x ^ 2 + 2 * (-69363073866) * x * y + 64738861720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 79529686180 64738861720 (-69363073866)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc41 (x y : ℝ) : 0 ≤ (358965127920 * x ^ 2 + 2 * (-317049593826) * x * y + 297050642880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 358965127920 297050642880 (-317049593826)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc42 (x y : ℝ) : 0 ≤ (593165310800 * x ^ 2 + 2 * (-530059262892) * x * y + 508283378000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 593165310800 508283378000 (-530059262892)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc43 (x y : ℝ) : 0 ≤ (424718441600 * x ^ 2 + 2 * (-383184135048) * x * y + 381534474560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 424718441600 381534474560 (-383184135048)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc44 (x y : ℝ) : 0 ≤ (110901781760 * x ^ 2 + 2 * (-100688609424) * x * y + 105398889920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 110901781760 105398889920 (-100688609424)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc45 (x y : ℝ) : 0 ≤ (54593850440 * x ^ 2 + 2 * (-50805842730) * x * y + 49084262220 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 54593850440 49084262220 (-50805842730)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc46 (x y : ℝ) : 0 ≤ (182522999000 * x ^ 2 + 2 * (-169736385612) * x * y + 164381042160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 182522999000 164381042160 (-169736385612)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc47 (x y : ℝ) : 0 ≤ (199079036160 * x ^ 2 + 2 * (-185153217840) * x * y + 183172827440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 199079036160 183172827440 (-185153217840)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc48 (x y : ℝ) : 0 ≤ (70745924320 * x ^ 2 + 2 * (-65739496224) * x * y + 67424628480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 70745924320 67424628480 (-65739496224)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc49 (x y : ℝ) : 0 ≤ (24623273060 * x ^ 2 + 2 * (-23835810708) * x * y + 23585381220 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 24623273060 23585381220 (-23835810708)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc50 (x y : ℝ) : 0 ≤ (54049738640 * x ^ 2 + 2 * (-51818589756) * x * y + 51458780560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 54049738640 51458780560 (-51818589756)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc51 (x y : ℝ) : 0 ≤ (29114982800 * x ^ 2 + 2 * (-27688385784) * x * y + 28084634000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 29114982800 28084634000 (-27688385784)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc52 (x y : ℝ) : 0 ≤ (6563470400 * x ^ 2 + 2 * (-6461362596) * x * y + 6499073600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6563470400 6499073600 (-6461362596)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc53 (x y : ℝ) : 0 ≤ (7088328000 * x ^ 2 + 2 * (-6873847920) * x * y + 6959534400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7088328000 6959534400 (-6873847920)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ASE_hc54 (x y : ℝ) : 0 ≤ (780436800 * x ^ 2 + 2 * (-767062440) * x * y + 780436800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 780436800 780436800 (-767062440)
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem B_ASE_entry11 (z w : ℝ) : 4423680 * Hdiag (1 - z / 2) ((1 - w) / 2) =
      801184320 * ((1 - z - w) ^ 9) +
      8214628800 * (w * (1 - z - w) ^ 8) +
      36441336000 * (w ^ 2 * (1 - z - w) ^ 7) +
      91489281600 * (w ^ 3 * (1 - z - w) ^ 6) +
      142481379840 * (w ^ 4 * (1 - z - w) ^ 5) +
      141421989120 * (w ^ 5 * (1 - z - w) ^ 4) +
      87917245440 * (w ^ 6 * (1 - z - w) ^ 3) +
      31795461120 * (w ^ 7 * (1 - z - w) ^ 2) +
      5472952320 * (w ^ 8 * (1 - z - w)) +
      192737280 * (w ^ 9) +
      6659768160 * (z * (1 - z - w) ^ 8) +
      60646594240 * (z * w * (1 - z - w) ^ 7) +
      235423411680 * (z * w ^ 2 * (1 - z - w) ^ 6) +
      507118147840 * (z * w ^ 3 * (1 - z - w) ^ 5) +
      659659999360 * (z * w ^ 4 * (1 - z - w) ^ 4) +
      526172846080 * (z * w ^ 5 * (1 - z - w) ^ 3) +
      247457405440 * (z * w ^ 6 * (1 - z - w) ^ 2) +
      60737986560 * (z * w ^ 7 * (1 - z - w)) +
      5474990080 * (z * w ^ 8) +
      24731126870 * (z ^ 2 * (1 - z - w) ^ 7) +
      197409465390 * (z ^ 2 * w * (1 - z - w) ^ 6) +
      657946610000 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      1183535463800 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      1235628716960 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      743250805280 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      235335540480 * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      29446259840 * (z ^ 2 * w ^ 7) +
      54548120435 * (z ^ 3 * (1 - z - w) ^ 6) +
      373454270660 * (z ^ 3 * w * (1 - z - w) ^ 5) +
      1037775174300 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      1495013327520 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      1173383726480 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      472784120640 * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      75537958720 * (z ^ 3 * w ^ 6) +
      79451682980 * (z ^ 4 * (1 - z - w) ^ 5) +
      451880195880 * (z ^ 4 * w * (1 - z - w) ^ 4) +
      1002011957360 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      1081077082560 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      565844359040 * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      114337192320 * (z ^ 4 * w ^ 5) +
      79529686180 * (z ^ 5 * (1 - z - w) ^ 4) +
      358965127920 * (z ^ 5 * w * (1 - z - w) ^ 3) +
      593165310800 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      424718441600 * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      110901781760 * (z ^ 5 * w ^ 4) +
      54593850440 * (z ^ 6 * (1 - z - w) ^ 3) +
      182522999000 * (z ^ 6 * w * (1 - z - w) ^ 2) +
      199079036160 * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      70745924320 * (z ^ 6 * w ^ 3) +
      24623273060 * (z ^ 7 * (1 - z - w) ^ 2) +
      54049738640 * (z ^ 7 * w * (1 - z - w)) +
      29114982800 * (z ^ 7 * w ^ 2) +
      6563470400 * (z ^ 8 * (1 - z - w)) +
      7088328000 * (z ^ 8 * w) +
      780436800 * (z ^ 9) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_ASE_entry22 (z w : ℝ) : 4423680 * Hdiag ((1 - w) / 2) (1 - z / 2) =
      268058655 * ((1 - z - w) ^ 9) +
      3173049120 * (w * (1 - z - w) ^ 8) +
      16173052200 * (w ^ 2 * (1 - z - w) ^ 7) +
      46429159680 * (w ^ 3 * (1 - z - w) ^ 6) +
      82527394560 * (w ^ 4 * (1 - z - w) ^ 5) +
      93954693120 * (w ^ 5 * (1 - z - w) ^ 4) +
      68211588480 * (w ^ 6 * (1 - z - w) ^ 3) +
      30182983680 * (w ^ 7 * (1 - z - w) ^ 2) +
      7247950080 * (w ^ 8 * (1 - z - w)) +
      688128000 * (w ^ 9) +
      2668414545 * (z * (1 - z - w) ^ 8) +
      27635018260 * (z * w * (1 - z - w) ^ 7) +
      121565829680 * (z * w ^ 2 * (1 - z - w) ^ 6) +
      295612856080 * (z * w ^ 3 * (1 - z - w) ^ 5) +
      433564336480 * (z * w ^ 4 * (1 - z - w) ^ 4) +
      391746174400 * (z * w ^ 5 * (1 - z - w) ^ 3) +
      212023863040 * (z * w ^ 6 * (1 - z - w) ^ 2) +
      62300025600 * (z * w ^ 7 * (1 - z - w)) +
      7471182080 * (z * w ^ 8) +
      12111070085 * (z ^ 2 * (1 - z - w) ^ 7) +
      106918811160 * (z ^ 2 * w * (1 - z - w) ^ 6) +
      394891295780 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      787188651920 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      911786934320 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      611770981760 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      219136635840 * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      32047020800 * (z ^ 2 * w ^ 7) +
      32521501695 * (z ^ 3 * (1 - z - w) ^ 6) +
      238451526660 * (z ^ 3 * w * (1 - z - w) ^ 5) +
      715975698860 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      1119956796960 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      958489932240 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      423899289920 * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      75298628160 * (z ^ 3 * w ^ 6) +
      56332131420 * (z ^ 4 * (1 - z - w) ^ 5) +
      333163531520 * (z ^ 4 * w * (1 - z - w) ^ 4) +
      779672365120 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      896060984800 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      503138530240 * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      109914167680 * (z ^ 4 * w ^ 5) +
      64738861720 * (z ^ 5 * (1 - z - w) ^ 4) +
      297050642880 * (z ^ 5 * w * (1 - z - w) ^ 3) +
      508283378000 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      381534474560 * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      105398889920 * (z ^ 5 * w ^ 4) +
      49084262220 * (z ^ 6 * (1 - z - w) ^ 3) +
      164381042160 * (z ^ 6 * w * (1 - z - w) ^ 2) +
      183172827440 * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      67424628480 * (z ^ 6 * w ^ 3) +
      23585381220 * (z ^ 7 * (1 - z - w) ^ 2) +
      51458780560 * (z ^ 7 * w * (1 - z - w)) +
      28084634000 * (z ^ 7 * w ^ 2) +
      6499073600 * (z ^ 8 * (1 - z - w)) +
      6959534400 * (z ^ 8 * w) +
      780436800 * (z ^ 9) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_ASE_entry12 (z w : ℝ) : 4423680 * Hmixed (1 - z / 2) ((1 - w) / 2) =
      (-411481728) * ((1 - z - w) ^ 9) +
      (-4609025856) * (w * (1 - z - w) ^ 8) +
      (-22148058240) * (w ^ 2 * (1 - z - w) ^ 7) +
      (-59794467648) * (w ^ 3 * (1 - z - w) ^ 6) +
      (-99599797632) * (w ^ 4 * (1 - z - w) ^ 5) +
      (-105489283584) * (w ^ 5 * (1 - z - w) ^ 4) +
      (-70186266624) * (w ^ 6 * (1 - z - w) ^ 3) +
      (-27574459392) * (w ^ 7 * (1 - z - w) ^ 2) +
      (-5447534592) * (w ^ 8 * (1 - z - w)) +
      (-325902336) * (w ^ 9) +
      (-3774480192) * (z * (1 - z - w) ^ 8) +
      (-37331662752) * (z * w * (1 - z - w) ^ 7) +
      (-155814545568) * (z * w ^ 2 * (1 - z - w) ^ 6) +
      (-357917622720) * (z * w ^ 3 * (1 - z - w) ^ 5) +
      (-493466728320) * (z * w ^ 4 * (1 - z - w) ^ 4) +
      (-415755199488) * (z * w ^ 5 * (1 - z - w) ^ 3) +
      (-206650360320) * (z * w ^ 6 * (1 - z - w) ^ 2) +
      (-54076234752) * (z * w ^ 7 * (1 - z - w)) +
      (-5374605312) * (z * w ^ 8) +
      (-15706834722) * (z ^ 2 * (1 - z - w) ^ 7) +
      (-134329715382) * (z ^ 2 * w * (1 - z - w) ^ 6) +
      (-475149772500) * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      (-900172885536) * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      (-983906926368) * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      (-617063256096) * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      (-203336929728) * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      (-26534885376) * (z ^ 2 * w ^ 7) +
      (-38984838126) * (z ^ 3 * (1 - z - w) ^ 6) +
      (-280638182172) * (z ^ 3 * w * (1 - z - w) ^ 5) +
      (-814280610348) * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      (-1217537869200) * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      (-986761126464) * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      (-408725519232) * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      (-66864259008) * (z ^ 3 * w ^ 6) +
      (-63339743556) * (z ^ 4 * (1 - z - w) ^ 5) +
      (-371289053736) * (z ^ 4 * w * (1 - z - w) ^ 4) +
      (-845391756012) * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      (-932931661272) * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      (-497405434032) * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      (-101908790112) * (z ^ 4 * w ^ 5) +
      (-69363073866) * (z ^ 5 * (1 - z - w) ^ 4) +
      (-317049593826) * (z ^ 5 * w * (1 - z - w) ^ 3) +
      (-530059262892) * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      (-383184135048) * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      (-100688609424) * (z ^ 5 * w ^ 4) +
      (-50805842730) * (z ^ 6 * (1 - z - w) ^ 3) +
      (-169736385612) * (z ^ 6 * w * (1 - z - w) ^ 2) +
      (-185153217840) * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      (-65739496224) * (z ^ 6 * w ^ 3) +
      (-23835810708) * (z ^ 7 * (1 - z - w) ^ 2) +
      (-51818589756) * (z ^ 7 * w * (1 - z - w)) +
      (-27688385784) * (z ^ 7 * w ^ 2) +
      (-6461362596) * (z ^ 8 * (1 - z - w)) +
      (-6873847920) * (z ^ 8 * w) +
      (-767062440) * (z ^ 9) := by
  simp only [Hmixed, mixedNumerator, Sbound, denominator, kappaB]
  ring
private def B_ASE_data (z w : ℝ) : List (ℝ × ℝ × ℝ × ℝ) :=
  [(801184320, 268058655, (-411481728), (1 - z - w) ^ 9),
  (8214628800, 3173049120, (-4609025856), w * (1 - z - w) ^ 8),
  (36441336000, 16173052200, (-22148058240), w ^ 2 * (1 - z - w) ^ 7),
  (91489281600, 46429159680, (-59794467648), w ^ 3 * (1 - z - w) ^ 6),
  (142481379840, 82527394560, (-99599797632), w ^ 4 * (1 - z - w) ^ 5),
  (141421989120, 93954693120, (-105489283584), w ^ 5 * (1 - z - w) ^ 4),
  (87917245440, 68211588480, (-70186266624), w ^ 6 * (1 - z - w) ^ 3),
  (31795461120, 30182983680, (-27574459392), w ^ 7 * (1 - z - w) ^ 2),
  (5472952320, 7247950080, (-5447534592), w ^ 8 * (1 - z - w)),
  (192737280, 688128000, (-325902336), w ^ 9),
  (6659768160, 2668414545, (-3774480192), z * (1 - z - w) ^ 8),
  (60646594240, 27635018260, (-37331662752), z * w * (1 - z - w) ^ 7),
  (235423411680, 121565829680, (-155814545568), z * w ^ 2 * (1 - z - w) ^ 6),
  (507118147840, 295612856080, (-357917622720), z * w ^ 3 * (1 - z - w) ^ 5),
  (659659999360, 433564336480, (-493466728320), z * w ^ 4 * (1 - z - w) ^ 4),
  (526172846080, 391746174400, (-415755199488), z * w ^ 5 * (1 - z - w) ^ 3),
  (247457405440, 212023863040, (-206650360320), z * w ^ 6 * (1 - z - w) ^ 2),
  (60737986560, 62300025600, (-54076234752), z * w ^ 7 * (1 - z - w)),
  (5474990080, 7471182080, (-5374605312), z * w ^ 8),
  (24731126870, 12111070085, (-15706834722), z ^ 2 * (1 - z - w) ^ 7),
  (197409465390, 106918811160, (-134329715382), z ^ 2 * w * (1 - z - w) ^ 6),
  (657946610000, 394891295780, (-475149772500), z ^ 2 * w ^ 2 * (1 - z - w) ^ 5),
  (1183535463800, 787188651920, (-900172885536), z ^ 2 * w ^ 3 * (1 - z - w) ^ 4),
  (1235628716960, 911786934320, (-983906926368), z ^ 2 * w ^ 4 * (1 - z - w) ^ 3),
  (743250805280, 611770981760, (-617063256096), z ^ 2 * w ^ 5 * (1 - z - w) ^ 2),
  (235335540480, 219136635840, (-203336929728), z ^ 2 * w ^ 6 * (1 - z - w)),
  (29446259840, 32047020800, (-26534885376), z ^ 2 * w ^ 7),
  (54548120435, 32521501695, (-38984838126), z ^ 3 * (1 - z - w) ^ 6),
  (373454270660, 238451526660, (-280638182172), z ^ 3 * w * (1 - z - w) ^ 5),
  (1037775174300, 715975698860, (-814280610348), z ^ 3 * w ^ 2 * (1 - z - w) ^ 4),
  (1495013327520, 1119956796960, (-1217537869200), z ^ 3 * w ^ 3 * (1 - z - w) ^ 3),
  (1173383726480, 958489932240, (-986761126464), z ^ 3 * w ^ 4 * (1 - z - w) ^ 2),
  (472784120640, 423899289920, (-408725519232), z ^ 3 * w ^ 5 * (1 - z - w)),
  (75537958720, 75298628160, (-66864259008), z ^ 3 * w ^ 6),
  (79451682980, 56332131420, (-63339743556), z ^ 4 * (1 - z - w) ^ 5),
  (451880195880, 333163531520, (-371289053736), z ^ 4 * w * (1 - z - w) ^ 4),
  (1002011957360, 779672365120, (-845391756012), z ^ 4 * w ^ 2 * (1 - z - w) ^ 3),
  (1081077082560, 896060984800, (-932931661272), z ^ 4 * w ^ 3 * (1 - z - w) ^ 2),
  (565844359040, 503138530240, (-497405434032), z ^ 4 * w ^ 4 * (1 - z - w)),
  (114337192320, 109914167680, (-101908790112), z ^ 4 * w ^ 5),
  (79529686180, 64738861720, (-69363073866), z ^ 5 * (1 - z - w) ^ 4),
  (358965127920, 297050642880, (-317049593826), z ^ 5 * w * (1 - z - w) ^ 3),
  (593165310800, 508283378000, (-530059262892), z ^ 5 * w ^ 2 * (1 - z - w) ^ 2),
  (424718441600, 381534474560, (-383184135048), z ^ 5 * w ^ 3 * (1 - z - w)),
  (110901781760, 105398889920, (-100688609424), z ^ 5 * w ^ 4),
  (54593850440, 49084262220, (-50805842730), z ^ 6 * (1 - z - w) ^ 3),
  (182522999000, 164381042160, (-169736385612), z ^ 6 * w * (1 - z - w) ^ 2),
  (199079036160, 183172827440, (-185153217840), z ^ 6 * w ^ 2 * (1 - z - w)),
  (70745924320, 67424628480, (-65739496224), z ^ 6 * w ^ 3),
  (24623273060, 23585381220, (-23835810708), z ^ 7 * (1 - z - w) ^ 2),
  (54049738640, 51458780560, (-51818589756), z ^ 7 * w * (1 - z - w)),
  (29114982800, 28084634000, (-27688385784), z ^ 7 * w ^ 2),
  (6563470400, 6499073600, (-6461362596), z ^ 8 * (1 - z - w)),
  (7088328000, 6959534400, (-6873847920), z ^ 8 * w),
  (780436800, 780436800, (-767062440), z ^ 9)]

private theorem B_ASE_entry11_list (z w : ℝ) :
    4423680 * Hdiag (1 - z / 2) ((1 - w) / 2) = ((B_ASE_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [B_ASE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_ASE_entry11 z w

private theorem B_ASE_entry22_list (z w : ℝ) :
    4423680 * Hdiag ((1 - w) / 2) (1 - z / 2) = ((B_ASE_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [B_ASE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_ASE_entry22 z w

private theorem B_ASE_entry12_list (z w : ℝ) :
    4423680 * Hmixed (1 - z / 2) ((1 - w) / 2) = ((B_ASE_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [B_ASE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_ASE_entry12 z w

private theorem B_ASE {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ Hdiag (1 - z / 2) ((1 - w) / 2) * x ^ 2 + 2 * Hmixed (1 - z / 2) ((1 - w) / 2) * x * y + Hdiag ((1 - w) / 2) (1 - z / 2) * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (B_ASE_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (B_ASE_hc0 x y) (by positivity),
      mul_nonneg (B_ASE_hc1 x y) (by positivity),
      mul_nonneg (B_ASE_hc2 x y) (by positivity),
      mul_nonneg (B_ASE_hc3 x y) (by positivity),
      mul_nonneg (B_ASE_hc4 x y) (by positivity),
      mul_nonneg (B_ASE_hc5 x y) (by positivity),
      mul_nonneg (B_ASE_hc6 x y) (by positivity),
      mul_nonneg (B_ASE_hc7 x y) (by positivity),
      mul_nonneg (B_ASE_hc8 x y) (by positivity),
      mul_nonneg (B_ASE_hc9 x y) (by positivity),
      mul_nonneg (B_ASE_hc10 x y) (by positivity),
      mul_nonneg (B_ASE_hc11 x y) (by positivity),
      mul_nonneg (B_ASE_hc12 x y) (by positivity),
      mul_nonneg (B_ASE_hc13 x y) (by positivity),
      mul_nonneg (B_ASE_hc14 x y) (by positivity),
      mul_nonneg (B_ASE_hc15 x y) (by positivity),
      mul_nonneg (B_ASE_hc16 x y) (by positivity),
      mul_nonneg (B_ASE_hc17 x y) (by positivity),
      mul_nonneg (B_ASE_hc18 x y) (by positivity),
      mul_nonneg (B_ASE_hc19 x y) (by positivity),
      mul_nonneg (B_ASE_hc20 x y) (by positivity),
      mul_nonneg (B_ASE_hc21 x y) (by positivity),
      mul_nonneg (B_ASE_hc22 x y) (by positivity),
      mul_nonneg (B_ASE_hc23 x y) (by positivity),
      mul_nonneg (B_ASE_hc24 x y) (by positivity),
      mul_nonneg (B_ASE_hc25 x y) (by positivity),
      mul_nonneg (B_ASE_hc26 x y) (by positivity),
      mul_nonneg (B_ASE_hc27 x y) (by positivity),
      mul_nonneg (B_ASE_hc28 x y) (by positivity),
      mul_nonneg (B_ASE_hc29 x y) (by positivity),
      mul_nonneg (B_ASE_hc30 x y) (by positivity),
      mul_nonneg (B_ASE_hc31 x y) (by positivity),
      mul_nonneg (B_ASE_hc32 x y) (by positivity),
      mul_nonneg (B_ASE_hc33 x y) (by positivity),
      mul_nonneg (B_ASE_hc34 x y) (by positivity),
      mul_nonneg (B_ASE_hc35 x y) (by positivity),
      mul_nonneg (B_ASE_hc36 x y) (by positivity),
      mul_nonneg (B_ASE_hc37 x y) (by positivity),
      mul_nonneg (B_ASE_hc38 x y) (by positivity),
      mul_nonneg (B_ASE_hc39 x y) (by positivity),
      mul_nonneg (B_ASE_hc40 x y) (by positivity),
      mul_nonneg (B_ASE_hc41 x y) (by positivity),
      mul_nonneg (B_ASE_hc42 x y) (by positivity),
      mul_nonneg (B_ASE_hc43 x y) (by positivity),
      mul_nonneg (B_ASE_hc44 x y) (by positivity),
      mul_nonneg (B_ASE_hc45 x y) (by positivity),
      mul_nonneg (B_ASE_hc46 x y) (by positivity),
      mul_nonneg (B_ASE_hc47 x y) (by positivity),
      mul_nonneg (B_ASE_hc48 x y) (by positivity),
      mul_nonneg (B_ASE_hc49 x y) (by positivity),
      mul_nonneg (B_ASE_hc50 x y) (by positivity),
      mul_nonneg (B_ASE_hc51 x y) (by positivity),
      mul_nonneg (B_ASE_hc52 x y) (by positivity),
      mul_nonneg (B_ASE_hc53 x y) (by positivity),
      mul_nonneg (B_ASE_hc54 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (B_ASE_data z w) x y hcoeff
  rw [← B_ASE_entry11_list, ← B_ASE_entry12_list, ← B_ASE_entry22_list] at hpos
  nlinarith only [hpos]

private theorem B_ACE_hc0 (x y : ℝ) : 0 ≤ (801184320 * x ^ 2 + 2 * (-411481728) * x * y + 268058655 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 801184320 268058655 (-411481728)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc1 (x y : ℝ) : 0 ≤ (7007873280 * x ^ 2 + 2 * (-3209126976) * x * y + 1920065325 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7007873280 1920065325 (-3209126976)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc2 (x y : ℝ) : 0 ≤ (26584506240 * x ^ 2 + 2 * (-10454658624) * x * y + 5656719270 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 26584506240 5656719270 (-10454658624)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc3 (x y : ℝ) : 0 ≤ (57424677120 * x ^ 2 + 2 * (-18240186432) * x * y + 8752198440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 57424677120 8752198440 (-18240186432)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc4 (x y : ℝ) : 0 ≤ (77762971200 * x ^ 2 + 2 * (-17789831232) * x * y + 7541591760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 77762971200 7541591760 (-17789831232)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc5 (x y : ℝ) : 0 ≤ (68316026880 * x ^ 2 + 2 * (-8488967808) * x * y + 3815876160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 68316026880 3815876160 (-8488967808)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc6 (x y : ℝ) : 0 ≤ (38811640320 * x ^ 2 + 2 * (-95439360) * x * y + 1914585600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 38811640320 1914585600 (-95439360)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc7 (x y : ℝ) : 0 ≤ (13695129600 * x ^ 2 + 2 * 1846354944 * x * y + 1661306880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 13695129600 1661306880 1846354944
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc8 (x y : ℝ) : 0 ≤ (2713436160 * x ^ 2 + 2 * 744124416 * x * y + 998522880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2713436160 998522880 744124416
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc9 (x y : ℝ) : 0 ≤ (230031360 * x ^ 2 + 2 * 84639744 * x * y + 230031360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 230031360 230031360 84639744
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc11 (x y : ℝ) : 0 ≤ (7460952480 * x ^ 2 + 2 * (-4185961920) * x * y + 2936473200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7460952480 2936473200 (-4185961920)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc12 (x y : ℝ) : 0 ≤ (58776153440 * x ^ 2 + 2 * (-29632145760) * x * y + 19380035675 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 58776153440 19380035675 (-29632145760)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc13 (x y : ℝ) : 0 ≤ (198552639840 * x ^ 2 + 2 * (-86630082240) * x * y + 52602330140 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 198552639840 52602330140 (-86630082240)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc14 (x y : ℝ) : 0 ≤ (376536997920 * x ^ 2 + 2 * (-133460600544) * x * y + 75570771320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 376536997920 75570771320 (-133460600544)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc15 (x y : ℝ) : 0 ≤ (439718296960 * x ^ 2 + 2 * (-111886516800) * x * y + 62284122400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 439718296960 62284122400 (-111886516800)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc16 (x y : ℝ) : 0 ≤ (325715961600 * x ^ 2 + 2 * (-42736161408) * x * y + 32202166400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 325715961600 32202166400 (-42736161408)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc17 (x y : ℝ) : 0 ≤ (151771100160 * x ^ 2 + 2 * 3055601664 * x * y + 14796600320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 151771100160 14796600320 3055601664
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc18 (x y : ℝ) : 0 ≤ (42612961280 * x ^ 2 + 2 * 8402734080 * x * y + 8175841280 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 42612961280 8175841280 8402734080
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc19 (x y : ℝ) : 0 ≤ (6599147520 * x ^ 2 + 2 * 2390065152 * x * y + 3169320960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6599147520 3169320960 2390065152
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc20 (x y : ℝ) : 0 ≤ (460062720 * x ^ 2 + 2 * 169279488 * x * y + 460062720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 460062720 460062720 169279488
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc21 (x y : ℝ) : 0 ≤ (31390895030 * x ^ 2 + 2 * (-19481314914) * x * y + 14779484630 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 31390895030 14779484630 (-19481314914)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc22 (x y : ℝ) : 0 ≤ (219467133980 * x ^ 2 + 2 * (-124332825768) * x * y + 89806854575 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 219467133980 89806854575 (-124332825768)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc23 (x y : ℝ) : 0 ≤ (647539119430 * x ^ 2 + 2 * (-324046323834) * x * y + 225369622110 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 647539119430 225369622110 (-324046323834)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc24 (x y : ℝ) : 0 ≤ (1049750930640 * x ^ 2 + 2 * (-438987322212) * x * y + 304175991480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1049750930640 304175991480 (-438987322212)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc25 (x y : ℝ) : 0 ≤ (1016981401520 * x ^ 2 + 2 * (-318758843664) * x * y + 245019006320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1016981401520 245019006320 (-318758843664)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc26 (x y : ℝ) : 0 ≤ (597909592000 * x ^ 2 + 2 * (-105398188128) * x * y + 129945733440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 597909592000 129945733440 (-105398188128)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc27 (x y : ℝ) : 0 ≤ (206063595520 * x ^ 2 + 2 * 1761926016 * x * y + 52889559040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 206063595520 52889559040 1761926016
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc28 (x y : ℝ) : 0 ≤ (37661306880 * x ^ 2 + 2 * 9822087168 * x * y + 16943493120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 37661306880 16943493120 9822087168
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc29 (x y : ℝ) : 0 ≤ (2813952000 * x ^ 2 + 2 * 1628307456 * x * y + 2813952000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2813952000 2813952000 1628307456
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc30 (x y : ℝ) : 0 ≤ (79279247305 * x ^ 2 + 2 * (-54691672848) * x * y + 44632571780 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 79279247305 44632571780 (-54691672848)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc31 (x y : ℝ) : 0 ≤ (484497605785 * x ^ 2 + 2 * (-311730684192) * x * y + 246964165405 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 484497605785 246964165405 (-311730684192)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc32 (x y : ℝ) : 0 ≤ (1223690550760 * x ^ 2 + 2 * (-716736256092) * x * y + 563752476640 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1223690550760 563752476640 (-716736256092)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc33 (x y : ℝ) : 0 ≤ (1648914440280 * x ^ 2 + 2 * (-845198541756) * x * y + 693673792760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1648914440280 693673792760 (-845198541756)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc34 (x y : ℝ) : 0 ≤ (1270957697600 * x ^ 2 + 2 * (-529916688240) * x * y + 509551208000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1270957697600 509551208000 (-529916688240)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc35 (x y : ℝ) : 0 ≤ (553853827840 * x ^ 2 + 2 * (-158525660640) * x * y + 236862688000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 553853827840 236862688000 (-158525660640)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc36 (x y : ℝ) : 0 ≤ (124036106240 * x ^ 2 + 2 * (-11903869440) * x * y + 70261647360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 124036106240 70261647360 (-11903869440)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc37 (x y : ℝ) : 0 ≤ (10697728000 * x ^ 2 + 2 * 2206679040 * x * y + 10697728000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 10697728000 10697728000 2206679040
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc38 (x y : ℝ) : 0 ≤ (133999803415 * x ^ 2 + 2 * (-102324581682) * x * y + 88853633115 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 133999803415 88853633115 (-102324581682)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc39 (x y : ℝ) : 0 ≤ (703211491460 * x ^ 2 + 2 * (-512628000720) * x * y + 438296407780 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 703211491460 438296407780 (-512628000720)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc40 (x y : ℝ) : 0 ≤ (1483794037240 * x ^ 2 + 2 * (-1017766526376) * x * y + 880557686400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1483794037240 880557686400 (-1017766526376)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc41 (x y : ℝ) : 0 ≤ (1603758818480 * x ^ 2 + 2 * (-1013083964844) * x * y + 933496331520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1603758818480 933496331520 (-1013083964844)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc42 (x y : ℝ) : 0 ≤ (928767682400 * x ^ 2 + 2 * (-521545831728) * x * y + 564123637600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 928767682400 564123637600 (-521545831728)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc43 (x y : ℝ) : 0 ≤ (269451366400 * x ^ 2 + 2 * (-125744474784) * x * y + 191617484800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 269451366400 191617484800 (-125744474784)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc44 (x y : ℝ) : 0 ≤ (29853414400 * x ^ 2 + 2 * (-9808763904) * x * y + 29853414400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 29853414400 29853414400 (-9808763904)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc45 (x y : ℝ) : 0 ≤ (158981369160 * x ^ 2 + 2 * (-132702817422) * x * y + 121070993140 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 158981369160 121070993140 (-132702817422)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc46 (x y : ℝ) : 0 ≤ (699438681620 * x ^ 2 + 2 * (-569326452792) * x * y + 515756895280 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 699438681620 515756895280 (-569326452792)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc47 (x y : ℝ) : 0 ≤ (1190397082640 * x ^ 2 + 2 * (-938999538186) * x * y + 868221822640 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1190397082640 868221822640 (-938999538186)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc48 (x y : ℝ) : 0 ≤ (975402834800 * x ^ 2 + 2 * (-740212696656) * x * y + 730966062960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 975402834800 730966062960 (-740212696656)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc49 (x y : ℝ) : 0 ≤ (381839208960 * x ^ 2 + 2 * (-276355602480) * x * y + 313815472640 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 381839208960 313815472640 (-276355602480)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc50 (x y : ℝ) : 0 ≤ (56389672960 * x ^ 2 + 2 * (-38526237120) * x * y + 56389672960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 56389672960 56389672960 (-38526237120)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc51 (x y : ℝ) : 0 ≤ (134123536620 * x ^ 2 + 2 * (-120168916596) * x * y + 113823123940 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 134123536620 113823123940 (-120168916596)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc52 (x y : ℝ) : 0 ≤ (476906315600 * x ^ 2 + 2 * (-423759510600) * x * y + 400069044260 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 476906315600 400069044260 (-423759510600)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc53 (x y : ℝ) : 0 ≤ (617240360680 * x ^ 2 + 2 * (-543451931640) * x * y + 524496538600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 617240360680 524496538600 (-543451931640)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc54 (x y : ℝ) : 0 ≤ (343495425280 * x ^ 2 + 2 * (-300022081320) * x * y + 307365658880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 343495425280 307365658880 (-300022081320)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc55 (x y : ℝ) : 0 ≤ (68951052800 * x ^ 2 + 2 * (-60037960992) * x * y + 68951052800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 68951052800 68951052800 (-60037960992)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc56 (x y : ℝ) : 0 ≤ (79217123500 * x ^ 2 + 2 * (-74641653438) * x * y + 72669643440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 79217123500 72669643440 (-74641653438)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc57 (x y : ℝ) : 0 ≤ (214106730300 * x ^ 2 + 2 * (-202459134552) * x * y + 196592656700 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 214106730300 196592656700 (-202459134552)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc58 (x y : ℝ) : 0 ≤ (188065196800 * x ^ 2 + 2 * (-178796890332) * x * y + 177051147520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 188065196800 177051147520 (-178796890332)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc59 (x y : ℝ) : 0 ≤ (53579553280 * x ^ 2 + 2 * (-51462587952) * x * y + 53579553280 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 53579553280 53579553280 (-51462587952)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc60 (x y : ℝ) : 0 ≤ (31186743460 * x ^ 2 + 2 * (-30297173304) * x * y + 30084454820 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 31186743460 30084454820 (-30297173304)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc61 (x y : ℝ) : 0 ≤ (57045436800 * x ^ 2 + 2 * (-56034892944) * x * y + 55420430720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 57045436800 55420430720 (-56034892944)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc62 (x y : ℝ) : 0 ≤ (25547210560 * x ^ 2 + 2 * (-25443326376) * x * y + 25547210560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 25547210560 25547210560 (-25443326376)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc63 (x y : ℝ) : 0 ≤ (7343907200 * x ^ 2 + 2 * (-7228425036) * x * y + 7279510400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7343907200 7279510400 (-7228425036)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc64 (x y : ℝ) : 0 ≤ (6819049600 * x ^ 2 + 2 * (-6815939712) * x * y + 6819049600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6819049600 6819049600 (-6815939712)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_ACE_hc65 (x y : ℝ) : 0 ≤ (780436800 * x ^ 2 + 2 * (-767062440) * x * y + 780436800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 780436800 780436800 (-767062440)
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem B_ACE_entry11 (z w : ℝ) : 4423680 * Hdiag (1 - z / 2) ((1 + w) / 2) =
      801184320 * ((1 - z - w) ^ 10) +
      7007873280 * (w * (1 - z - w) ^ 9) +
      26584506240 * (w ^ 2 * (1 - z - w) ^ 8) +
      57424677120 * (w ^ 3 * (1 - z - w) ^ 7) +
      77762971200 * (w ^ 4 * (1 - z - w) ^ 6) +
      68316026880 * (w ^ 5 * (1 - z - w) ^ 5) +
      38811640320 * (w ^ 6 * (1 - z - w) ^ 4) +
      13695129600 * (w ^ 7 * (1 - z - w) ^ 3) +
      2713436160 * (w ^ 8 * (1 - z - w) ^ 2) +
      230031360 * (w ^ 9 * (1 - z - w)) +
      7460952480 * (z * (1 - z - w) ^ 9) +
      58776153440 * (z * w * (1 - z - w) ^ 8) +
      198552639840 * (z * w ^ 2 * (1 - z - w) ^ 7) +
      376536997920 * (z * w ^ 3 * (1 - z - w) ^ 6) +
      439718296960 * (z * w ^ 4 * (1 - z - w) ^ 5) +
      325715961600 * (z * w ^ 5 * (1 - z - w) ^ 4) +
      151771100160 * (z * w ^ 6 * (1 - z - w) ^ 3) +
      42612961280 * (z * w ^ 7 * (1 - z - w) ^ 2) +
      6599147520 * (z * w ^ 8 * (1 - z - w)) +
      460062720 * (z * w ^ 9) +
      31390895030 * (z ^ 2 * (1 - z - w) ^ 8) +
      219467133980 * (z ^ 2 * w * (1 - z - w) ^ 7) +
      647539119430 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 6) +
      1049750930640 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 5) +
      1016981401520 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 4) +
      597909592000 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 3) +
      206063595520 * (z ^ 2 * w ^ 6 * (1 - z - w) ^ 2) +
      37661306880 * (z ^ 2 * w ^ 7 * (1 - z - w)) +
      2813952000 * (z ^ 2 * w ^ 8) +
      79279247305 * (z ^ 3 * (1 - z - w) ^ 7) +
      484497605785 * (z ^ 3 * w * (1 - z - w) ^ 6) +
      1223690550760 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 5) +
      1648914440280 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 4) +
      1270957697600 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 3) +
      553853827840 * (z ^ 3 * w ^ 5 * (1 - z - w) ^ 2) +
      124036106240 * (z ^ 3 * w ^ 6 * (1 - z - w)) +
      10697728000 * (z ^ 3 * w ^ 7) +
      133999803415 * (z ^ 4 * (1 - z - w) ^ 6) +
      703211491460 * (z ^ 4 * w * (1 - z - w) ^ 5) +
      1483794037240 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 4) +
      1603758818480 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 3) +
      928767682400 * (z ^ 4 * w ^ 4 * (1 - z - w) ^ 2) +
      269451366400 * (z ^ 4 * w ^ 5 * (1 - z - w)) +
      29853414400 * (z ^ 4 * w ^ 6) +
      158981369160 * (z ^ 5 * (1 - z - w) ^ 5) +
      699438681620 * (z ^ 5 * w * (1 - z - w) ^ 4) +
      1190397082640 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 3) +
      975402834800 * (z ^ 5 * w ^ 3 * (1 - z - w) ^ 2) +
      381839208960 * (z ^ 5 * w ^ 4 * (1 - z - w)) +
      56389672960 * (z ^ 5 * w ^ 5) +
      134123536620 * (z ^ 6 * (1 - z - w) ^ 4) +
      476906315600 * (z ^ 6 * w * (1 - z - w) ^ 3) +
      617240360680 * (z ^ 6 * w ^ 2 * (1 - z - w) ^ 2) +
      343495425280 * (z ^ 6 * w ^ 3 * (1 - z - w)) +
      68951052800 * (z ^ 6 * w ^ 4) +
      79217123500 * (z ^ 7 * (1 - z - w) ^ 3) +
      214106730300 * (z ^ 7 * w * (1 - z - w) ^ 2) +
      188065196800 * (z ^ 7 * w ^ 2 * (1 - z - w)) +
      53579553280 * (z ^ 7 * w ^ 3) +
      31186743460 * (z ^ 8 * (1 - z - w) ^ 2) +
      57045436800 * (z ^ 8 * w * (1 - z - w)) +
      25547210560 * (z ^ 8 * w ^ 2) +
      7343907200 * (z ^ 9 * (1 - z - w)) +
      6819049600 * (z ^ 9 * w) +
      780436800 * (z ^ 10) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_ACE_entry22 (z w : ℝ) : 4423680 * Hdiag ((1 + w) / 2) (1 - z / 2) =
      268058655 * ((1 - z - w) ^ 10) +
      1920065325 * (w * (1 - z - w) ^ 9) +
      5656719270 * (w ^ 2 * (1 - z - w) ^ 8) +
      8752198440 * (w ^ 3 * (1 - z - w) ^ 7) +
      7541591760 * (w ^ 4 * (1 - z - w) ^ 6) +
      3815876160 * (w ^ 5 * (1 - z - w) ^ 5) +
      1914585600 * (w ^ 6 * (1 - z - w) ^ 4) +
      1661306880 * (w ^ 7 * (1 - z - w) ^ 3) +
      998522880 * (w ^ 8 * (1 - z - w) ^ 2) +
      230031360 * (w ^ 9 * (1 - z - w)) +
      2936473200 * (z * (1 - z - w) ^ 9) +
      19380035675 * (z * w * (1 - z - w) ^ 8) +
      52602330140 * (z * w ^ 2 * (1 - z - w) ^ 7) +
      75570771320 * (z * w ^ 3 * (1 - z - w) ^ 6) +
      62284122400 * (z * w ^ 4 * (1 - z - w) ^ 5) +
      32202166400 * (z * w ^ 5 * (1 - z - w) ^ 4) +
      14796600320 * (z * w ^ 6 * (1 - z - w) ^ 3) +
      8175841280 * (z * w ^ 7 * (1 - z - w) ^ 2) +
      3169320960 * (z * w ^ 8 * (1 - z - w)) +
      460062720 * (z * w ^ 9) +
      14779484630 * (z ^ 2 * (1 - z - w) ^ 8) +
      89806854575 * (z ^ 2 * w * (1 - z - w) ^ 7) +
      225369622110 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 6) +
      304175991480 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 5) +
      245019006320 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 4) +
      129945733440 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 3) +
      52889559040 * (z ^ 2 * w ^ 6 * (1 - z - w) ^ 2) +
      16943493120 * (z ^ 2 * w ^ 7 * (1 - z - w)) +
      2813952000 * (z ^ 2 * w ^ 8) +
      44632571780 * (z ^ 3 * (1 - z - w) ^ 7) +
      246964165405 * (z ^ 3 * w * (1 - z - w) ^ 6) +
      563752476640 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 5) +
      693673792760 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 4) +
      509551208000 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 3) +
      236862688000 * (z ^ 3 * w ^ 5 * (1 - z - w) ^ 2) +
      70261647360 * (z ^ 3 * w ^ 6 * (1 - z - w)) +
      10697728000 * (z ^ 3 * w ^ 7) +
      88853633115 * (z ^ 4 * (1 - z - w) ^ 6) +
      438296407780 * (z ^ 4 * w * (1 - z - w) ^ 5) +
      880557686400 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 4) +
      933496331520 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 3) +
      564123637600 * (z ^ 4 * w ^ 4 * (1 - z - w) ^ 2) +
      191617484800 * (z ^ 4 * w ^ 5 * (1 - z - w)) +
      29853414400 * (z ^ 4 * w ^ 6) +
      121070993140 * (z ^ 5 * (1 - z - w) ^ 5) +
      515756895280 * (z ^ 5 * w * (1 - z - w) ^ 4) +
      868221822640 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 3) +
      730966062960 * (z ^ 5 * w ^ 3 * (1 - z - w) ^ 2) +
      313815472640 * (z ^ 5 * w ^ 4 * (1 - z - w)) +
      56389672960 * (z ^ 5 * w ^ 5) +
      113823123940 * (z ^ 6 * (1 - z - w) ^ 4) +
      400069044260 * (z ^ 6 * w * (1 - z - w) ^ 3) +
      524496538600 * (z ^ 6 * w ^ 2 * (1 - z - w) ^ 2) +
      307365658880 * (z ^ 6 * w ^ 3 * (1 - z - w)) +
      68951052800 * (z ^ 6 * w ^ 4) +
      72669643440 * (z ^ 7 * (1 - z - w) ^ 3) +
      196592656700 * (z ^ 7 * w * (1 - z - w) ^ 2) +
      177051147520 * (z ^ 7 * w ^ 2 * (1 - z - w)) +
      53579553280 * (z ^ 7 * w ^ 3) +
      30084454820 * (z ^ 8 * (1 - z - w) ^ 2) +
      55420430720 * (z ^ 8 * w * (1 - z - w)) +
      25547210560 * (z ^ 8 * w ^ 2) +
      7279510400 * (z ^ 9 * (1 - z - w)) +
      6819049600 * (z ^ 9 * w) +
      780436800 * (z ^ 10) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_ACE_entry12 (z w : ℝ) : 4423680 * Hmixed (1 - z / 2) ((1 + w) / 2) =
      (-411481728) * ((1 - z - w) ^ 10) +
      (-3209126976) * (w * (1 - z - w) ^ 9) +
      (-10454658624) * (w ^ 2 * (1 - z - w) ^ 8) +
      (-18240186432) * (w ^ 3 * (1 - z - w) ^ 7) +
      (-17789831232) * (w ^ 4 * (1 - z - w) ^ 6) +
      (-8488967808) * (w ^ 5 * (1 - z - w) ^ 5) +
      (-95439360) * (w ^ 6 * (1 - z - w) ^ 4) +
      1846354944 * (w ^ 7 * (1 - z - w) ^ 3) +
      744124416 * (w ^ 8 * (1 - z - w) ^ 2) +
      84639744 * (w ^ 9 * (1 - z - w)) +
      (-4185961920) * (z * (1 - z - w) ^ 9) +
      (-29632145760) * (z * w * (1 - z - w) ^ 8) +
      (-86630082240) * (z * w ^ 2 * (1 - z - w) ^ 7) +
      (-133460600544) * (z * w ^ 3 * (1 - z - w) ^ 6) +
      (-111886516800) * (z * w ^ 4 * (1 - z - w) ^ 5) +
      (-42736161408) * (z * w ^ 5 * (1 - z - w) ^ 4) +
      3055601664 * (z * w ^ 6 * (1 - z - w) ^ 3) +
      8402734080 * (z * w ^ 7 * (1 - z - w) ^ 2) +
      2390065152 * (z * w ^ 8 * (1 - z - w)) +
      169279488 * (z * w ^ 9) +
      (-19481314914) * (z ^ 2 * (1 - z - w) ^ 8) +
      (-124332825768) * (z ^ 2 * w * (1 - z - w) ^ 7) +
      (-324046323834) * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 6) +
      (-438987322212) * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 5) +
      (-318758843664) * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 4) +
      (-105398188128) * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 3) +
      1761926016 * (z ^ 2 * w ^ 6 * (1 - z - w) ^ 2) +
      9822087168 * (z ^ 2 * w ^ 7 * (1 - z - w)) +
      1628307456 * (z ^ 2 * w ^ 8) +
      (-54691672848) * (z ^ 3 * (1 - z - w) ^ 7) +
      (-311730684192) * (z ^ 3 * w * (1 - z - w) ^ 6) +
      (-716736256092) * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 5) +
      (-845198541756) * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 4) +
      (-529916688240) * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 3) +
      (-158525660640) * (z ^ 3 * w ^ 5 * (1 - z - w) ^ 2) +
      (-11903869440) * (z ^ 3 * w ^ 6 * (1 - z - w)) +
      2206679040 * (z ^ 3 * w ^ 7) +
      (-102324581682) * (z ^ 4 * (1 - z - w) ^ 6) +
      (-512628000720) * (z ^ 4 * w * (1 - z - w) ^ 5) +
      (-1017766526376) * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 4) +
      (-1013083964844) * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 3) +
      (-521545831728) * (z ^ 4 * w ^ 4 * (1 - z - w) ^ 2) +
      (-125744474784) * (z ^ 4 * w ^ 5 * (1 - z - w)) +
      (-9808763904) * (z ^ 4 * w ^ 6) +
      (-132702817422) * (z ^ 5 * (1 - z - w) ^ 5) +
      (-569326452792) * (z ^ 5 * w * (1 - z - w) ^ 4) +
      (-938999538186) * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 3) +
      (-740212696656) * (z ^ 5 * w ^ 3 * (1 - z - w) ^ 2) +
      (-276355602480) * (z ^ 5 * w ^ 4 * (1 - z - w)) +
      (-38526237120) * (z ^ 5 * w ^ 5) +
      (-120168916596) * (z ^ 6 * (1 - z - w) ^ 4) +
      (-423759510600) * (z ^ 6 * w * (1 - z - w) ^ 3) +
      (-543451931640) * (z ^ 6 * w ^ 2 * (1 - z - w) ^ 2) +
      (-300022081320) * (z ^ 6 * w ^ 3 * (1 - z - w)) +
      (-60037960992) * (z ^ 6 * w ^ 4) +
      (-74641653438) * (z ^ 7 * (1 - z - w) ^ 3) +
      (-202459134552) * (z ^ 7 * w * (1 - z - w) ^ 2) +
      (-178796890332) * (z ^ 7 * w ^ 2 * (1 - z - w)) +
      (-51462587952) * (z ^ 7 * w ^ 3) +
      (-30297173304) * (z ^ 8 * (1 - z - w) ^ 2) +
      (-56034892944) * (z ^ 8 * w * (1 - z - w)) +
      (-25443326376) * (z ^ 8 * w ^ 2) +
      (-7228425036) * (z ^ 9 * (1 - z - w)) +
      (-6815939712) * (z ^ 9 * w) +
      (-767062440) * (z ^ 10) := by
  simp only [Hmixed, mixedNumerator, Sbound, denominator, kappaB]
  ring
private def B_ACE_data (z w : ℝ) : List (ℝ × ℝ × ℝ × ℝ) :=
  [(801184320, 268058655, (-411481728), (1 - z - w) ^ 10),
  (7007873280, 1920065325, (-3209126976), w * (1 - z - w) ^ 9),
  (26584506240, 5656719270, (-10454658624), w ^ 2 * (1 - z - w) ^ 8),
  (57424677120, 8752198440, (-18240186432), w ^ 3 * (1 - z - w) ^ 7),
  (77762971200, 7541591760, (-17789831232), w ^ 4 * (1 - z - w) ^ 6),
  (68316026880, 3815876160, (-8488967808), w ^ 5 * (1 - z - w) ^ 5),
  (38811640320, 1914585600, (-95439360), w ^ 6 * (1 - z - w) ^ 4),
  (13695129600, 1661306880, 1846354944, w ^ 7 * (1 - z - w) ^ 3),
  (2713436160, 998522880, 744124416, w ^ 8 * (1 - z - w) ^ 2),
  (230031360, 230031360, 84639744, w ^ 9 * (1 - z - w)),
  (7460952480, 2936473200, (-4185961920), z * (1 - z - w) ^ 9),
  (58776153440, 19380035675, (-29632145760), z * w * (1 - z - w) ^ 8),
  (198552639840, 52602330140, (-86630082240), z * w ^ 2 * (1 - z - w) ^ 7),
  (376536997920, 75570771320, (-133460600544), z * w ^ 3 * (1 - z - w) ^ 6),
  (439718296960, 62284122400, (-111886516800), z * w ^ 4 * (1 - z - w) ^ 5),
  (325715961600, 32202166400, (-42736161408), z * w ^ 5 * (1 - z - w) ^ 4),
  (151771100160, 14796600320, 3055601664, z * w ^ 6 * (1 - z - w) ^ 3),
  (42612961280, 8175841280, 8402734080, z * w ^ 7 * (1 - z - w) ^ 2),
  (6599147520, 3169320960, 2390065152, z * w ^ 8 * (1 - z - w)),
  (460062720, 460062720, 169279488, z * w ^ 9),
  (31390895030, 14779484630, (-19481314914), z ^ 2 * (1 - z - w) ^ 8),
  (219467133980, 89806854575, (-124332825768), z ^ 2 * w * (1 - z - w) ^ 7),
  (647539119430, 225369622110, (-324046323834), z ^ 2 * w ^ 2 * (1 - z - w) ^ 6),
  (1049750930640, 304175991480, (-438987322212), z ^ 2 * w ^ 3 * (1 - z - w) ^ 5),
  (1016981401520, 245019006320, (-318758843664), z ^ 2 * w ^ 4 * (1 - z - w) ^ 4),
  (597909592000, 129945733440, (-105398188128), z ^ 2 * w ^ 5 * (1 - z - w) ^ 3),
  (206063595520, 52889559040, 1761926016, z ^ 2 * w ^ 6 * (1 - z - w) ^ 2),
  (37661306880, 16943493120, 9822087168, z ^ 2 * w ^ 7 * (1 - z - w)),
  (2813952000, 2813952000, 1628307456, z ^ 2 * w ^ 8),
  (79279247305, 44632571780, (-54691672848), z ^ 3 * (1 - z - w) ^ 7),
  (484497605785, 246964165405, (-311730684192), z ^ 3 * w * (1 - z - w) ^ 6),
  (1223690550760, 563752476640, (-716736256092), z ^ 3 * w ^ 2 * (1 - z - w) ^ 5),
  (1648914440280, 693673792760, (-845198541756), z ^ 3 * w ^ 3 * (1 - z - w) ^ 4),
  (1270957697600, 509551208000, (-529916688240), z ^ 3 * w ^ 4 * (1 - z - w) ^ 3),
  (553853827840, 236862688000, (-158525660640), z ^ 3 * w ^ 5 * (1 - z - w) ^ 2),
  (124036106240, 70261647360, (-11903869440), z ^ 3 * w ^ 6 * (1 - z - w)),
  (10697728000, 10697728000, 2206679040, z ^ 3 * w ^ 7),
  (133999803415, 88853633115, (-102324581682), z ^ 4 * (1 - z - w) ^ 6),
  (703211491460, 438296407780, (-512628000720), z ^ 4 * w * (1 - z - w) ^ 5),
  (1483794037240, 880557686400, (-1017766526376), z ^ 4 * w ^ 2 * (1 - z - w) ^ 4),
  (1603758818480, 933496331520, (-1013083964844), z ^ 4 * w ^ 3 * (1 - z - w) ^ 3),
  (928767682400, 564123637600, (-521545831728), z ^ 4 * w ^ 4 * (1 - z - w) ^ 2),
  (269451366400, 191617484800, (-125744474784), z ^ 4 * w ^ 5 * (1 - z - w)),
  (29853414400, 29853414400, (-9808763904), z ^ 4 * w ^ 6),
  (158981369160, 121070993140, (-132702817422), z ^ 5 * (1 - z - w) ^ 5),
  (699438681620, 515756895280, (-569326452792), z ^ 5 * w * (1 - z - w) ^ 4),
  (1190397082640, 868221822640, (-938999538186), z ^ 5 * w ^ 2 * (1 - z - w) ^ 3),
  (975402834800, 730966062960, (-740212696656), z ^ 5 * w ^ 3 * (1 - z - w) ^ 2),
  (381839208960, 313815472640, (-276355602480), z ^ 5 * w ^ 4 * (1 - z - w)),
  (56389672960, 56389672960, (-38526237120), z ^ 5 * w ^ 5),
  (134123536620, 113823123940, (-120168916596), z ^ 6 * (1 - z - w) ^ 4),
  (476906315600, 400069044260, (-423759510600), z ^ 6 * w * (1 - z - w) ^ 3),
  (617240360680, 524496538600, (-543451931640), z ^ 6 * w ^ 2 * (1 - z - w) ^ 2),
  (343495425280, 307365658880, (-300022081320), z ^ 6 * w ^ 3 * (1 - z - w)),
  (68951052800, 68951052800, (-60037960992), z ^ 6 * w ^ 4),
  (79217123500, 72669643440, (-74641653438), z ^ 7 * (1 - z - w) ^ 3),
  (214106730300, 196592656700, (-202459134552), z ^ 7 * w * (1 - z - w) ^ 2),
  (188065196800, 177051147520, (-178796890332), z ^ 7 * w ^ 2 * (1 - z - w)),
  (53579553280, 53579553280, (-51462587952), z ^ 7 * w ^ 3),
  (31186743460, 30084454820, (-30297173304), z ^ 8 * (1 - z - w) ^ 2),
  (57045436800, 55420430720, (-56034892944), z ^ 8 * w * (1 - z - w)),
  (25547210560, 25547210560, (-25443326376), z ^ 8 * w ^ 2),
  (7343907200, 7279510400, (-7228425036), z ^ 9 * (1 - z - w)),
  (6819049600, 6819049600, (-6815939712), z ^ 9 * w),
  (780436800, 780436800, (-767062440), z ^ 10)]

private theorem B_ACE_entry11_list (z w : ℝ) :
    4423680 * Hdiag (1 - z / 2) ((1 + w) / 2) = ((B_ACE_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [B_ACE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_ACE_entry11 z w

private theorem B_ACE_entry22_list (z w : ℝ) :
    4423680 * Hdiag ((1 + w) / 2) (1 - z / 2) = ((B_ACE_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [B_ACE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_ACE_entry22 z w

private theorem B_ACE_entry12_list (z w : ℝ) :
    4423680 * Hmixed (1 - z / 2) ((1 + w) / 2) = ((B_ACE_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [B_ACE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_ACE_entry12 z w

private theorem B_ACE {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ Hdiag (1 - z / 2) ((1 + w) / 2) * x ^ 2 + 2 * Hmixed (1 - z / 2) ((1 + w) / 2) * x * y + Hdiag ((1 + w) / 2) (1 - z / 2) * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (B_ACE_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (B_ACE_hc0 x y) (by positivity),
      mul_nonneg (B_ACE_hc1 x y) (by positivity),
      mul_nonneg (B_ACE_hc2 x y) (by positivity),
      mul_nonneg (B_ACE_hc3 x y) (by positivity),
      mul_nonneg (B_ACE_hc4 x y) (by positivity),
      mul_nonneg (B_ACE_hc5 x y) (by positivity),
      mul_nonneg (B_ACE_hc6 x y) (by positivity),
      mul_nonneg (B_ACE_hc7 x y) (by positivity),
      mul_nonneg (B_ACE_hc8 x y) (by positivity),
      mul_nonneg (B_ACE_hc9 x y) (by positivity),
      mul_nonneg (B_ACE_hc11 x y) (by positivity),
      mul_nonneg (B_ACE_hc12 x y) (by positivity),
      mul_nonneg (B_ACE_hc13 x y) (by positivity),
      mul_nonneg (B_ACE_hc14 x y) (by positivity),
      mul_nonneg (B_ACE_hc15 x y) (by positivity),
      mul_nonneg (B_ACE_hc16 x y) (by positivity),
      mul_nonneg (B_ACE_hc17 x y) (by positivity),
      mul_nonneg (B_ACE_hc18 x y) (by positivity),
      mul_nonneg (B_ACE_hc19 x y) (by positivity),
      mul_nonneg (B_ACE_hc20 x y) (by positivity),
      mul_nonneg (B_ACE_hc21 x y) (by positivity),
      mul_nonneg (B_ACE_hc22 x y) (by positivity),
      mul_nonneg (B_ACE_hc23 x y) (by positivity),
      mul_nonneg (B_ACE_hc24 x y) (by positivity),
      mul_nonneg (B_ACE_hc25 x y) (by positivity),
      mul_nonneg (B_ACE_hc26 x y) (by positivity),
      mul_nonneg (B_ACE_hc27 x y) (by positivity),
      mul_nonneg (B_ACE_hc28 x y) (by positivity),
      mul_nonneg (B_ACE_hc29 x y) (by positivity),
      mul_nonneg (B_ACE_hc30 x y) (by positivity),
      mul_nonneg (B_ACE_hc31 x y) (by positivity),
      mul_nonneg (B_ACE_hc32 x y) (by positivity),
      mul_nonneg (B_ACE_hc33 x y) (by positivity),
      mul_nonneg (B_ACE_hc34 x y) (by positivity),
      mul_nonneg (B_ACE_hc35 x y) (by positivity),
      mul_nonneg (B_ACE_hc36 x y) (by positivity),
      mul_nonneg (B_ACE_hc37 x y) (by positivity),
      mul_nonneg (B_ACE_hc38 x y) (by positivity),
      mul_nonneg (B_ACE_hc39 x y) (by positivity),
      mul_nonneg (B_ACE_hc40 x y) (by positivity),
      mul_nonneg (B_ACE_hc41 x y) (by positivity),
      mul_nonneg (B_ACE_hc42 x y) (by positivity),
      mul_nonneg (B_ACE_hc43 x y) (by positivity),
      mul_nonneg (B_ACE_hc44 x y) (by positivity),
      mul_nonneg (B_ACE_hc45 x y) (by positivity),
      mul_nonneg (B_ACE_hc46 x y) (by positivity),
      mul_nonneg (B_ACE_hc47 x y) (by positivity),
      mul_nonneg (B_ACE_hc48 x y) (by positivity),
      mul_nonneg (B_ACE_hc49 x y) (by positivity),
      mul_nonneg (B_ACE_hc50 x y) (by positivity),
      mul_nonneg (B_ACE_hc51 x y) (by positivity),
      mul_nonneg (B_ACE_hc52 x y) (by positivity),
      mul_nonneg (B_ACE_hc53 x y) (by positivity),
      mul_nonneg (B_ACE_hc54 x y) (by positivity),
      mul_nonneg (B_ACE_hc55 x y) (by positivity),
      mul_nonneg (B_ACE_hc56 x y) (by positivity),
      mul_nonneg (B_ACE_hc57 x y) (by positivity),
      mul_nonneg (B_ACE_hc58 x y) (by positivity),
      mul_nonneg (B_ACE_hc59 x y) (by positivity),
      mul_nonneg (B_ACE_hc60 x y) (by positivity),
      mul_nonneg (B_ACE_hc61 x y) (by positivity),
      mul_nonneg (B_ACE_hc62 x y) (by positivity),
      mul_nonneg (B_ACE_hc63 x y) (by positivity),
      mul_nonneg (B_ACE_hc64 x y) (by positivity),
      mul_nonneg (B_ACE_hc65 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (B_ACE_data z w) x y hcoeff
  rw [← B_ACE_entry11_list, ← B_ACE_entry12_list, ← B_ACE_entry22_list] at hpos
  nlinarith only [hpos]

private theorem B_SBE_hc0 (x y : ℝ) : 0 ≤ (801184320 * x ^ 2 + 2 * (-411481728) * x * y + 268058655 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 801184320 268058655 (-411481728)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc1 (x y : ℝ) : 0 ≤ (7761549600 * x ^ 2 + 2 * (-3632190912) * x * y + 2156641245 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7761549600 2156641245 (-3632190912)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc2 (x y : ℝ) : 0 ≤ (33545378390 * x ^ 2 + 2 * (-14568520482) * x * y + 8016883685 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 33545378390 8016883685 (-14568520482)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc3 (x y : ℝ) : 0 ≤ (84189484865 * x ^ 2 + 2 * (-34684787694) * x * y + 18306466615 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 84189484865 18306466615 (-34684787694)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc4 (x y : ℝ) : 0 ≤ (133900348280 * x ^ 2 + 2 * (-53475840324) * x * y + 28360530540 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 133900348280 28360530540 (-53475840324)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc5 (x y : ℝ) : 0 ≤ (138250280160 * x ^ 2 + 2 * (-54534308550) * x * y + 30580181140 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 138250280160 30580181140 (-54534308550)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc6 (x y : ℝ) : 0 ≤ (91017819400 * x ^ 2 + 2 * (-36001603866) * x * y + 22502066300 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 91017819400 22502066300 (-36001603866)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc7 (x y : ℝ) : 0 ≤ (35683155740 * x ^ 2 + 2 * (-14336038872) * x * y + 10652132340 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 35683155740 10652132340 (-14336038872)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc8 (x y : ℝ) : 0 ≤ (7013055760 * x ^ 2 + 2 * (-2908573260) * x * y + 2877353600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7013055760 2877353600 (-2908573260)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc9 (x y : ℝ) : 0 ≤ (393346160 * x ^ 2 + 2 * (-178693632) * x * y + 329471440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 393346160 329471440 (-178693632)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc10 (x y : ℝ) : 0 ≤ (8214628800 * x ^ 2 + 2 * (-4609025856) * x * y + 3173049120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 8214628800 3173049120 (-4609025856)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc11 (x y : ℝ) : 0 ≤ (70787466560 * x ^ 2 + 2 * (-36412750944) * x * y + 23133767660 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 70787466560 23133767660 (-36412750944)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc12 (x y : ℝ) : 0 ≤ (268395571630 * x ^ 2 + 2 * (-127897332726) * x * y + 75410056960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 268395571630 75410056960 (-127897332726)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc13 (x y : ℝ) : 0 ≤ (581299100260 * x ^ 2 + 2 * (-260302314732) * x * y + 144758679180 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 581299100260 144758679180 (-260302314732)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc14 (x y : ℝ) : 0 ≤ (781243281480 * x ^ 2 + 2 * (-333933543096) * x * y + 179786836120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 781243281480 179786836120 (-333933543096)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc15 (x y : ℝ) : 0 ≤ (661942110320 * x ^ 2 + 2 * (-274133203134) * x * y + 147700125920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 661942110320 147700125920 (-274133203134)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc16 (x y : ℝ) : 0 ≤ (341890453720 * x ^ 2 + 2 * (-138950194848) * x * y + 77766239280 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 341890453720 77766239280 (-138950194848)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc17 (x y : ℝ) : 0 ≤ (97008364240 * x ^ 2 + 2 * (-39089889564) * x * y + 23694410480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 97008364240 23694410480 (-39089889564)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc18 (x y : ℝ) : 0 ≤ (11292991360 * x ^ 2 + 2 * (-4548061848) * x * y + 3150801760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 11292991360 3150801760 (-4548061848)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc19 (x y : ℝ) : 0 ≤ (36441336000 * x ^ 2 + 2 * (-22148058240) * x * y + 16173052200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 36441336000 16173052200 (-22148058240)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc20 (x y : ℝ) : 0 ≤ (274755292320 * x ^ 2 + 2 * (-154258269792) * x * y + 104856901120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 274755292320 104856901120 (-154258269792)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc21 (x y : ℝ) : 0 ≤ (893937893840 * x ^ 2 + 2 * (-465812117844) * x * y + 294637724420 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 893937893840 294637724420 (-465812117844)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc22 (x y : ℝ) : 0 ≤ (1619860304900 * x ^ 2 + 2 * (-789800687772) * x * y + 467442094140 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1619860304900 467442094140 (-789800687772)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc23 (x y : ℝ) : 0 ≤ (1757077254160 * x ^ 2 + 2 * (-809723096748) * x * y + 453895088640 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1757077254160 453895088640 (-809723096748)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc24 (x y : ℝ) : 0 ≤ (1134990038960 * x ^ 2 + 2 * (-499542625788) * x * y + 270129657680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1134990038960 270129657680 (-499542625788)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc25 (x y : ℝ) : 0 ≤ (401907989120 * x ^ 2 + 2 * (-170556849744) * x * y + 91077082800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 401907989120 91077082800 (-170556849744)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc26 (x y : ℝ) : 0 ≤ (59758896880 * x ^ 2 + 2 * (-24638539224) * x * y + 13354295120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 59758896880 13354295120 (-24638539224)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc27 (x y : ℝ) : 0 ≤ (91489281600 * x ^ 2 + 2 * (-59794467648) * x * y + 46429159680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 91489281600 46429159680 (-59794467648)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc28 (x y : ℝ) : 0 ≤ (590753231360 * x ^ 2 + 2 * (-359615989056) * x * y + 261537060080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 590753231360 261537060080 (-359615989056)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc29 (x y : ℝ) : 0 ≤ (1601710881400 * x ^ 2 + 2 * (-908664717216) * x * y + 616809671920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1601710881400 616809671920 (-908664717216)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc30 (x y : ℝ) : 0 ≤ (2326829525280 * x ^ 2 + 2 * (-1234255129968) * x * y + 781703724000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2326829525280 781703724000 (-1234255129968)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc31 (x y : ℝ) : 0 ≤ (1903824005440 * x ^ 2 + 2 * (-949116116856) * x * y + 562817685920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1903824005440 562817685920 (-949116116856)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc32 (x y : ℝ) : 0 ≤ (829055040000 * x ^ 2 + 2 * (-390748387608) * x * y + 218634934720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 829055040000 218634934720 (-390748387608)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc33 (x y : ℝ) : 0 ≤ (149611463520 * x ^ 2 + 2 * (-67043088624) * x * y + 35818498560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 149611463520 35818498560 (-67043088624)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc34 (x y : ℝ) : 0 ≤ (142481379840 * x ^ 2 + 2 * (-99599797632) * x * y + 82527394560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 142481379840 82527394560 (-99599797632)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc35 (x y : ℝ) : 0 ≤ (765153799040 * x ^ 2 + 2 * (-502531248000) * x * y + 391709609120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 765153799040 391709609120 (-502531248000)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc36 (x y : ℝ) : 0 ≤ (1657603915680 * x ^ 2 + 2 * (-1020165005088) * x * y + 744368024880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1657603915680 744368024880 (-1020165005088)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc37 (x y : ℝ) : 0 ≤ (1807058977840 * x ^ 2 + 2 * (-1041462762624) * x * y + 708879162960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1807058977840 708879162960 (-1041462762624)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc38 (x y : ℝ) : 0 ≤ (989244464320 * x ^ 2 + 2 * (-534292548912) * x * y + 338754810560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 989244464320 338754810560 (-534292548912)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc39 (x y : ℝ) : 0 ≤ (217125931200 * x ^ 2 + 2 * (-110059034832) * x * y + 65061158400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 217125931200 65061158400 (-110059034832)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc40 (x y : ℝ) : 0 ≤ (141421989120 * x ^ 2 + 2 * (-105489283584) * x * y + 93954693120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 141421989120 93954693120 (-105489283584)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc41 (x y : ℝ) : 0 ≤ (605203066880 * x ^ 2 + 2 * (-428159069184) * x * y + 359891370560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 605203066880 359891370560 (-428159069184)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc42 (x y : ℝ) : 0 ≤ (980341467680 * x ^ 2 + 2 * (-654274865184) * x * y + 516206570240 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 980341467680 516206570240 (-654274865184)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc43 (x y : ℝ) : 0 ≤ (711648599360 * x ^ 2 + 2 * (-446122185984) * x * y + 328780724160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 711648599360 328780724160 (-446122185984)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc44 (x y : ℝ) : 0 ≤ (195141229440 * x ^ 2 + 2 * (-114497717472) * x * y + 78505209600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 195141229440 78505209600 (-114497717472)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc45 (x y : ℝ) : 0 ≤ (87917245440 * x ^ 2 + 2 * (-70186266624) * x * y + 68211588480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 87917245440 68211588480 (-70186266624)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc46 (x y : ℝ) : 0 ≤ (280046067200 * x ^ 2 + 2 * (-214467239424) * x * y + 197245667840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 280046067200 197245667840 (-214467239424)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc47 (x y : ℝ) : 0 ≤ (300512864000 * x ^ 2 + 2 * (-218970687936) * x * y + 189580245440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 300512864000 189580245440 (-218970687936)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc48 (x y : ℝ) : 0 ≤ (108641464000 * x ^ 2 + 2 * (-74698292160) * x * y + 60571899200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 108641464000 60571899200 (-74698292160)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc49 (x y : ℝ) : 0 ≤ (31795461120 * x ^ 2 + 2 * (-27574459392) * x * y + 30182983680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 31795461120 30182983680 (-27574459392)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc50 (x y : ℝ) : 0 ≤ (66443857920 * x ^ 2 + 2 * (-56221602816) * x * y + 58431909120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 66443857920 58431909120 (-56221602816)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc51 (x y : ℝ) : 0 ≤ (35152131200 * x ^ 2 + 2 * (-28680253440) * x * y + 28178904320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 35152131200 28178904320 (-28680253440)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc52 (x y : ℝ) : 0 ≤ (5472952320 * x ^ 2 + 2 * (-5447534592) * x * y + 7247950080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 5472952320 7247950080 (-5447534592)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc53 (x y : ℝ) : 0 ≤ (5470914560 * x ^ 2 + 2 * (-5520463872) * x * y + 7024718080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 5470914560 7024718080 (-5520463872)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SBE_hc54 (x y : ℝ) : 0 ≤ (192737280 * x ^ 2 + 2 * (-325902336) * x * y + 688128000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 192737280 688128000 (-325902336)
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem B_SBE_entry11 (z w : ℝ) : 4423680 * Hdiag (1 + w / 2) ((1 - z) / 2) =
      801184320 * ((1 - z - w) ^ 9) +
      7761549600 * (w * (1 - z - w) ^ 8) +
      33545378390 * (w ^ 2 * (1 - z - w) ^ 7) +
      84189484865 * (w ^ 3 * (1 - z - w) ^ 6) +
      133900348280 * (w ^ 4 * (1 - z - w) ^ 5) +
      138250280160 * (w ^ 5 * (1 - z - w) ^ 4) +
      91017819400 * (w ^ 6 * (1 - z - w) ^ 3) +
      35683155740 * (w ^ 7 * (1 - z - w) ^ 2) +
      7013055760 * (w ^ 8 * (1 - z - w)) +
      393346160 * (w ^ 9) +
      8214628800 * (z * (1 - z - w) ^ 8) +
      70787466560 * (z * w * (1 - z - w) ^ 7) +
      268395571630 * (z * w ^ 2 * (1 - z - w) ^ 6) +
      581299100260 * (z * w ^ 3 * (1 - z - w) ^ 5) +
      781243281480 * (z * w ^ 4 * (1 - z - w) ^ 4) +
      661942110320 * (z * w ^ 5 * (1 - z - w) ^ 3) +
      341890453720 * (z * w ^ 6 * (1 - z - w) ^ 2) +
      97008364240 * (z * w ^ 7 * (1 - z - w)) +
      11292991360 * (z * w ^ 8) +
      36441336000 * (z ^ 2 * (1 - z - w) ^ 7) +
      274755292320 * (z ^ 2 * w * (1 - z - w) ^ 6) +
      893937893840 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      1619860304900 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      1757077254160 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      1134990038960 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      401907989120 * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      59758896880 * (z ^ 2 * w ^ 7) +
      91489281600 * (z ^ 3 * (1 - z - w) ^ 6) +
      590753231360 * (z ^ 3 * w * (1 - z - w) ^ 5) +
      1601710881400 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      2326829525280 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      1903824005440 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      829055040000 * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      149611463520 * (z ^ 3 * w ^ 6) +
      142481379840 * (z ^ 4 * (1 - z - w) ^ 5) +
      765153799040 * (z ^ 4 * w * (1 - z - w) ^ 4) +
      1657603915680 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      1807058977840 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      989244464320 * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      217125931200 * (z ^ 4 * w ^ 5) +
      141421989120 * (z ^ 5 * (1 - z - w) ^ 4) +
      605203066880 * (z ^ 5 * w * (1 - z - w) ^ 3) +
      980341467680 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      711648599360 * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      195141229440 * (z ^ 5 * w ^ 4) +
      87917245440 * (z ^ 6 * (1 - z - w) ^ 3) +
      280046067200 * (z ^ 6 * w * (1 - z - w) ^ 2) +
      300512864000 * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      108641464000 * (z ^ 6 * w ^ 3) +
      31795461120 * (z ^ 7 * (1 - z - w) ^ 2) +
      66443857920 * (z ^ 7 * w * (1 - z - w)) +
      35152131200 * (z ^ 7 * w ^ 2) +
      5472952320 * (z ^ 8 * (1 - z - w)) +
      5470914560 * (z ^ 8 * w) +
      192737280 * (z ^ 9) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_SBE_entry22 (z w : ℝ) : 4423680 * Hdiag ((1 - z) / 2) (1 + w / 2) =
      268058655 * ((1 - z - w) ^ 9) +
      2156641245 * (w * (1 - z - w) ^ 8) +
      8016883685 * (w ^ 2 * (1 - z - w) ^ 7) +
      18306466615 * (w ^ 3 * (1 - z - w) ^ 6) +
      28360530540 * (w ^ 4 * (1 - z - w) ^ 5) +
      30580181140 * (w ^ 5 * (1 - z - w) ^ 4) +
      22502066300 * (w ^ 6 * (1 - z - w) ^ 3) +
      10652132340 * (w ^ 7 * (1 - z - w) ^ 2) +
      2877353600 * (w ^ 8 * (1 - z - w)) +
      329471440 * (w ^ 9) +
      3173049120 * (z * (1 - z - w) ^ 8) +
      23133767660 * (z * w * (1 - z - w) ^ 7) +
      75410056960 * (z * w ^ 2 * (1 - z - w) ^ 6) +
      144758679180 * (z * w ^ 3 * (1 - z - w) ^ 5) +
      179786836120 * (z * w ^ 4 * (1 - z - w) ^ 4) +
      147700125920 * (z * w ^ 5 * (1 - z - w) ^ 3) +
      77766239280 * (z * w ^ 6 * (1 - z - w) ^ 2) +
      23694410480 * (z * w ^ 7 * (1 - z - w)) +
      3150801760 * (z * w ^ 8) +
      16173052200 * (z ^ 2 * (1 - z - w) ^ 7) +
      104856901120 * (z ^ 2 * w * (1 - z - w) ^ 6) +
      294637724420 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      467442094140 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      453895088640 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      270129657680 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      91077082800 * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      13354295120 * (z ^ 2 * w ^ 7) +
      46429159680 * (z ^ 3 * (1 - z - w) ^ 6) +
      261537060080 * (z ^ 3 * w * (1 - z - w) ^ 5) +
      616809671920 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      781703724000 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      562817685920 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      218634934720 * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      35818498560 * (z ^ 3 * w ^ 6) +
      82527394560 * (z ^ 4 * (1 - z - w) ^ 5) +
      391709609120 * (z ^ 4 * w * (1 - z - w) ^ 4) +
      744368024880 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      708879162960 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      338754810560 * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      65061158400 * (z ^ 4 * w ^ 5) +
      93954693120 * (z ^ 5 * (1 - z - w) ^ 4) +
      359891370560 * (z ^ 5 * w * (1 - z - w) ^ 3) +
      516206570240 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      328780724160 * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      78505209600 * (z ^ 5 * w ^ 4) +
      68211588480 * (z ^ 6 * (1 - z - w) ^ 3) +
      197245667840 * (z ^ 6 * w * (1 - z - w) ^ 2) +
      189580245440 * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      60571899200 * (z ^ 6 * w ^ 3) +
      30182983680 * (z ^ 7 * (1 - z - w) ^ 2) +
      58431909120 * (z ^ 7 * w * (1 - z - w)) +
      28178904320 * (z ^ 7 * w ^ 2) +
      7247950080 * (z ^ 8 * (1 - z - w)) +
      7024718080 * (z ^ 8 * w) +
      688128000 * (z ^ 9) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_SBE_entry12 (z w : ℝ) : 4423680 * Hmixed (1 + w / 2) ((1 - z) / 2) =
      (-411481728) * ((1 - z - w) ^ 9) +
      (-3632190912) * (w * (1 - z - w) ^ 8) +
      (-14568520482) * (w ^ 2 * (1 - z - w) ^ 7) +
      (-34684787694) * (w ^ 3 * (1 - z - w) ^ 6) +
      (-53475840324) * (w ^ 4 * (1 - z - w) ^ 5) +
      (-54534308550) * (w ^ 5 * (1 - z - w) ^ 4) +
      (-36001603866) * (w ^ 6 * (1 - z - w) ^ 3) +
      (-14336038872) * (w ^ 7 * (1 - z - w) ^ 2) +
      (-2908573260) * (w ^ 8 * (1 - z - w)) +
      (-178693632) * (w ^ 9) +
      (-4609025856) * (z * (1 - z - w) ^ 8) +
      (-36412750944) * (z * w * (1 - z - w) ^ 7) +
      (-127897332726) * (z * w ^ 2 * (1 - z - w) ^ 6) +
      (-260302314732) * (z * w ^ 3 * (1 - z - w) ^ 5) +
      (-333933543096) * (z * w ^ 4 * (1 - z - w) ^ 4) +
      (-274133203134) * (z * w ^ 5 * (1 - z - w) ^ 3) +
      (-138950194848) * (z * w ^ 6 * (1 - z - w) ^ 2) +
      (-39089889564) * (z * w ^ 7 * (1 - z - w)) +
      (-4548061848) * (z * w ^ 8) +
      (-22148058240) * (z ^ 2 * (1 - z - w) ^ 7) +
      (-154258269792) * (z ^ 2 * w * (1 - z - w) ^ 6) +
      (-465812117844) * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      (-789800687772) * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      (-809723096748) * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      (-499542625788) * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      (-170556849744) * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      (-24638539224) * (z ^ 2 * w ^ 7) +
      (-59794467648) * (z ^ 3 * (1 - z - w) ^ 6) +
      (-359615989056) * (z ^ 3 * w * (1 - z - w) ^ 5) +
      (-908664717216) * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      (-1234255129968) * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      (-949116116856) * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      (-390748387608) * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      (-67043088624) * (z ^ 3 * w ^ 6) +
      (-99599797632) * (z ^ 4 * (1 - z - w) ^ 5) +
      (-502531248000) * (z ^ 4 * w * (1 - z - w) ^ 4) +
      (-1020165005088) * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      (-1041462762624) * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      (-534292548912) * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      (-110059034832) * (z ^ 4 * w ^ 5) +
      (-105489283584) * (z ^ 5 * (1 - z - w) ^ 4) +
      (-428159069184) * (z ^ 5 * w * (1 - z - w) ^ 3) +
      (-654274865184) * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      (-446122185984) * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      (-114497717472) * (z ^ 5 * w ^ 4) +
      (-70186266624) * (z ^ 6 * (1 - z - w) ^ 3) +
      (-214467239424) * (z ^ 6 * w * (1 - z - w) ^ 2) +
      (-218970687936) * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      (-74698292160) * (z ^ 6 * w ^ 3) +
      (-27574459392) * (z ^ 7 * (1 - z - w) ^ 2) +
      (-56221602816) * (z ^ 7 * w * (1 - z - w)) +
      (-28680253440) * (z ^ 7 * w ^ 2) +
      (-5447534592) * (z ^ 8 * (1 - z - w)) +
      (-5520463872) * (z ^ 8 * w) +
      (-325902336) * (z ^ 9) := by
  simp only [Hmixed, mixedNumerator, Sbound, denominator, kappaB]
  ring
private def B_SBE_data (z w : ℝ) : List (ℝ × ℝ × ℝ × ℝ) :=
  [(801184320, 268058655, (-411481728), (1 - z - w) ^ 9),
  (7761549600, 2156641245, (-3632190912), w * (1 - z - w) ^ 8),
  (33545378390, 8016883685, (-14568520482), w ^ 2 * (1 - z - w) ^ 7),
  (84189484865, 18306466615, (-34684787694), w ^ 3 * (1 - z - w) ^ 6),
  (133900348280, 28360530540, (-53475840324), w ^ 4 * (1 - z - w) ^ 5),
  (138250280160, 30580181140, (-54534308550), w ^ 5 * (1 - z - w) ^ 4),
  (91017819400, 22502066300, (-36001603866), w ^ 6 * (1 - z - w) ^ 3),
  (35683155740, 10652132340, (-14336038872), w ^ 7 * (1 - z - w) ^ 2),
  (7013055760, 2877353600, (-2908573260), w ^ 8 * (1 - z - w)),
  (393346160, 329471440, (-178693632), w ^ 9),
  (8214628800, 3173049120, (-4609025856), z * (1 - z - w) ^ 8),
  (70787466560, 23133767660, (-36412750944), z * w * (1 - z - w) ^ 7),
  (268395571630, 75410056960, (-127897332726), z * w ^ 2 * (1 - z - w) ^ 6),
  (581299100260, 144758679180, (-260302314732), z * w ^ 3 * (1 - z - w) ^ 5),
  (781243281480, 179786836120, (-333933543096), z * w ^ 4 * (1 - z - w) ^ 4),
  (661942110320, 147700125920, (-274133203134), z * w ^ 5 * (1 - z - w) ^ 3),
  (341890453720, 77766239280, (-138950194848), z * w ^ 6 * (1 - z - w) ^ 2),
  (97008364240, 23694410480, (-39089889564), z * w ^ 7 * (1 - z - w)),
  (11292991360, 3150801760, (-4548061848), z * w ^ 8),
  (36441336000, 16173052200, (-22148058240), z ^ 2 * (1 - z - w) ^ 7),
  (274755292320, 104856901120, (-154258269792), z ^ 2 * w * (1 - z - w) ^ 6),
  (893937893840, 294637724420, (-465812117844), z ^ 2 * w ^ 2 * (1 - z - w) ^ 5),
  (1619860304900, 467442094140, (-789800687772), z ^ 2 * w ^ 3 * (1 - z - w) ^ 4),
  (1757077254160, 453895088640, (-809723096748), z ^ 2 * w ^ 4 * (1 - z - w) ^ 3),
  (1134990038960, 270129657680, (-499542625788), z ^ 2 * w ^ 5 * (1 - z - w) ^ 2),
  (401907989120, 91077082800, (-170556849744), z ^ 2 * w ^ 6 * (1 - z - w)),
  (59758896880, 13354295120, (-24638539224), z ^ 2 * w ^ 7),
  (91489281600, 46429159680, (-59794467648), z ^ 3 * (1 - z - w) ^ 6),
  (590753231360, 261537060080, (-359615989056), z ^ 3 * w * (1 - z - w) ^ 5),
  (1601710881400, 616809671920, (-908664717216), z ^ 3 * w ^ 2 * (1 - z - w) ^ 4),
  (2326829525280, 781703724000, (-1234255129968), z ^ 3 * w ^ 3 * (1 - z - w) ^ 3),
  (1903824005440, 562817685920, (-949116116856), z ^ 3 * w ^ 4 * (1 - z - w) ^ 2),
  (829055040000, 218634934720, (-390748387608), z ^ 3 * w ^ 5 * (1 - z - w)),
  (149611463520, 35818498560, (-67043088624), z ^ 3 * w ^ 6),
  (142481379840, 82527394560, (-99599797632), z ^ 4 * (1 - z - w) ^ 5),
  (765153799040, 391709609120, (-502531248000), z ^ 4 * w * (1 - z - w) ^ 4),
  (1657603915680, 744368024880, (-1020165005088), z ^ 4 * w ^ 2 * (1 - z - w) ^ 3),
  (1807058977840, 708879162960, (-1041462762624), z ^ 4 * w ^ 3 * (1 - z - w) ^ 2),
  (989244464320, 338754810560, (-534292548912), z ^ 4 * w ^ 4 * (1 - z - w)),
  (217125931200, 65061158400, (-110059034832), z ^ 4 * w ^ 5),
  (141421989120, 93954693120, (-105489283584), z ^ 5 * (1 - z - w) ^ 4),
  (605203066880, 359891370560, (-428159069184), z ^ 5 * w * (1 - z - w) ^ 3),
  (980341467680, 516206570240, (-654274865184), z ^ 5 * w ^ 2 * (1 - z - w) ^ 2),
  (711648599360, 328780724160, (-446122185984), z ^ 5 * w ^ 3 * (1 - z - w)),
  (195141229440, 78505209600, (-114497717472), z ^ 5 * w ^ 4),
  (87917245440, 68211588480, (-70186266624), z ^ 6 * (1 - z - w) ^ 3),
  (280046067200, 197245667840, (-214467239424), z ^ 6 * w * (1 - z - w) ^ 2),
  (300512864000, 189580245440, (-218970687936), z ^ 6 * w ^ 2 * (1 - z - w)),
  (108641464000, 60571899200, (-74698292160), z ^ 6 * w ^ 3),
  (31795461120, 30182983680, (-27574459392), z ^ 7 * (1 - z - w) ^ 2),
  (66443857920, 58431909120, (-56221602816), z ^ 7 * w * (1 - z - w)),
  (35152131200, 28178904320, (-28680253440), z ^ 7 * w ^ 2),
  (5472952320, 7247950080, (-5447534592), z ^ 8 * (1 - z - w)),
  (5470914560, 7024718080, (-5520463872), z ^ 8 * w),
  (192737280, 688128000, (-325902336), z ^ 9)]

private theorem B_SBE_entry11_list (z w : ℝ) :
    4423680 * Hdiag (1 + w / 2) ((1 - z) / 2) = ((B_SBE_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [B_SBE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_SBE_entry11 z w

private theorem B_SBE_entry22_list (z w : ℝ) :
    4423680 * Hdiag ((1 - z) / 2) (1 + w / 2) = ((B_SBE_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [B_SBE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_SBE_entry22 z w

private theorem B_SBE_entry12_list (z w : ℝ) :
    4423680 * Hmixed (1 + w / 2) ((1 - z) / 2) = ((B_SBE_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [B_SBE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_SBE_entry12 z w

private theorem B_SBE {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ Hdiag (1 + w / 2) ((1 - z) / 2) * x ^ 2 + 2 * Hmixed (1 + w / 2) ((1 - z) / 2) * x * y + Hdiag ((1 - z) / 2) (1 + w / 2) * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (B_SBE_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (B_SBE_hc0 x y) (by positivity),
      mul_nonneg (B_SBE_hc1 x y) (by positivity),
      mul_nonneg (B_SBE_hc2 x y) (by positivity),
      mul_nonneg (B_SBE_hc3 x y) (by positivity),
      mul_nonneg (B_SBE_hc4 x y) (by positivity),
      mul_nonneg (B_SBE_hc5 x y) (by positivity),
      mul_nonneg (B_SBE_hc6 x y) (by positivity),
      mul_nonneg (B_SBE_hc7 x y) (by positivity),
      mul_nonneg (B_SBE_hc8 x y) (by positivity),
      mul_nonneg (B_SBE_hc9 x y) (by positivity),
      mul_nonneg (B_SBE_hc10 x y) (by positivity),
      mul_nonneg (B_SBE_hc11 x y) (by positivity),
      mul_nonneg (B_SBE_hc12 x y) (by positivity),
      mul_nonneg (B_SBE_hc13 x y) (by positivity),
      mul_nonneg (B_SBE_hc14 x y) (by positivity),
      mul_nonneg (B_SBE_hc15 x y) (by positivity),
      mul_nonneg (B_SBE_hc16 x y) (by positivity),
      mul_nonneg (B_SBE_hc17 x y) (by positivity),
      mul_nonneg (B_SBE_hc18 x y) (by positivity),
      mul_nonneg (B_SBE_hc19 x y) (by positivity),
      mul_nonneg (B_SBE_hc20 x y) (by positivity),
      mul_nonneg (B_SBE_hc21 x y) (by positivity),
      mul_nonneg (B_SBE_hc22 x y) (by positivity),
      mul_nonneg (B_SBE_hc23 x y) (by positivity),
      mul_nonneg (B_SBE_hc24 x y) (by positivity),
      mul_nonneg (B_SBE_hc25 x y) (by positivity),
      mul_nonneg (B_SBE_hc26 x y) (by positivity),
      mul_nonneg (B_SBE_hc27 x y) (by positivity),
      mul_nonneg (B_SBE_hc28 x y) (by positivity),
      mul_nonneg (B_SBE_hc29 x y) (by positivity),
      mul_nonneg (B_SBE_hc30 x y) (by positivity),
      mul_nonneg (B_SBE_hc31 x y) (by positivity),
      mul_nonneg (B_SBE_hc32 x y) (by positivity),
      mul_nonneg (B_SBE_hc33 x y) (by positivity),
      mul_nonneg (B_SBE_hc34 x y) (by positivity),
      mul_nonneg (B_SBE_hc35 x y) (by positivity),
      mul_nonneg (B_SBE_hc36 x y) (by positivity),
      mul_nonneg (B_SBE_hc37 x y) (by positivity),
      mul_nonneg (B_SBE_hc38 x y) (by positivity),
      mul_nonneg (B_SBE_hc39 x y) (by positivity),
      mul_nonneg (B_SBE_hc40 x y) (by positivity),
      mul_nonneg (B_SBE_hc41 x y) (by positivity),
      mul_nonneg (B_SBE_hc42 x y) (by positivity),
      mul_nonneg (B_SBE_hc43 x y) (by positivity),
      mul_nonneg (B_SBE_hc44 x y) (by positivity),
      mul_nonneg (B_SBE_hc45 x y) (by positivity),
      mul_nonneg (B_SBE_hc46 x y) (by positivity),
      mul_nonneg (B_SBE_hc47 x y) (by positivity),
      mul_nonneg (B_SBE_hc48 x y) (by positivity),
      mul_nonneg (B_SBE_hc49 x y) (by positivity),
      mul_nonneg (B_SBE_hc50 x y) (by positivity),
      mul_nonneg (B_SBE_hc51 x y) (by positivity),
      mul_nonneg (B_SBE_hc52 x y) (by positivity),
      mul_nonneg (B_SBE_hc53 x y) (by positivity),
      mul_nonneg (B_SBE_hc54 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (B_SBE_data z w) x y hcoeff
  rw [← B_SBE_entry11_list, ← B_SBE_entry12_list, ← B_SBE_entry22_list] at hpos
  nlinarith only [hpos]

private theorem B_CBE_hc0 (x y : ℝ) : 0 ≤ (801184320 * x ^ 2 + 2 * (-411481728) * x * y + 268058655 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 801184320 268058655 (-411481728)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc1 (x y : ℝ) : 0 ≤ (8562733920 * x ^ 2 + 2 * (-4043672640) * x * y + 2424699900 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 8562733920 2424699900 (-4043672640)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc2 (x y : ℝ) : 0 ≤ (41306927990 * x ^ 2 + 2 * (-18200711394) * x * y + 10173524930 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 41306927990 10173524930 (-18200711394)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc3 (x y : ℝ) : 0 ≤ (117734863255 * x ^ 2 + 2 * (-49253308176) * x * y + 26323350300 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 117734863255 26323350300 (-49253308176)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc4 (x y : ℝ) : 0 ≤ (218089833145 * x ^ 2 + 2 * (-88160628018) * x * y + 46666997155 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 218089833145 46666997155 (-88160628018)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc5 (x y : ℝ) : 0 ≤ (272150628440 * x ^ 2 + 2 * (-108010148874) * x * y + 58940711680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 272150628440 58940711680 (-108010148874)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc6 (x y : ℝ) : 0 ≤ (229268099560 * x ^ 2 + 2 * (-90535912416) * x * y + 53082247440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 229268099560 53082247440 (-90535912416)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc7 (x y : ℝ) : 0 ≤ (126700975140 * x ^ 2 + 2 * (-50337642738) * x * y + 33154198640 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 126700975140 33154198640 (-50337642738)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc8 (x y : ℝ) : 0 ≤ (42696211500 * x ^ 2 + 2 * (-17244612132) * x * y + 13529485940 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 42696211500 13529485940 (-17244612132)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc9 (x y : ℝ) : 0 ≤ (7406401920 * x ^ 2 + 2 * (-3087266892) * x * y + 3206825040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7406401920 3206825040 (-3087266892)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc10 (x y : ℝ) : 0 ≤ (393346160 * x ^ 2 + 2 * (-178693632) * x * y + 329471440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 393346160 329471440 (-178693632)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc11 (x y : ℝ) : 0 ≤ (7007873280 * x ^ 2 + 2 * (-3209126976) * x * y + 1920065325 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7007873280 1920065325 (-3209126976)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc12 (x y : ℝ) : 0 ≤ (67365565600 * x ^ 2 + 2 * (-28132139808) * x * y + 15181140175 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 67365565600 15181140175 (-28132139808)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc13 (x y : ℝ) : 0 ≤ (288182431260 * x ^ 2 + 2 * (-112332778152) * x * y + 56215690575 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 288182431260 56215690575 (-112332778152)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc14 (x y : ℝ) : 0 ≤ (714403928815 * x ^ 2 + 2 * (-266661879312) * x * y + 130051701445 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 714403928815 130051701445 (-266661879312)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc15 (x y : ℝ) : 0 ≤ (1120635267720 * x ^ 2 + 2 * (-410215838064) * x * y + 207097920020 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1120635267720 207097920020 (-410215838064)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc16 (x y : ℝ) : 0 ≤ (1140070612440 * x ^ 2 + 2 * (-417500433960) * x * y + 231339973620 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1140070612440 231339973620 (-417500433960)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc17 (x y : ℝ) : 0 ≤ (739294413040 * x ^ 2 + 2 * (-275202297480) * x * y + 176689548020 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 739294413040 176689548020 (-275202297480)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc18 (x y : ℝ) : 0 ≤ (285623877140 * x ^ 2 + 2 * (-109649733144) * x * y + 86812409740 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 285623877140 86812409740 (-109649733144)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc19 (x y : ℝ) : 0 ≤ (55470434640 * x ^ 2 + 2 * (-22431923856) * x * y + 24395377920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 55470434640 24395377920 (-22431923856)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc20 (x y : ℝ) : 0 ≤ (3126466320 * x ^ 2 + 2 * (-1447778304) * x * y + 2933376880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3126466320 2933376880 (-1447778304)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc21 (x y : ℝ) : 0 ≤ (26584506240 * x ^ 2 + 2 * (-10454658624) * x * y + 5656719270 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 26584506240 5656719270 (-10454658624)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc22 (x y : ℝ) : 0 ≤ (226799460000 * x ^ 2 + 2 * (-80644455744) * x * y + 37905178180 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 226799460000 37905178180 (-80644455744)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc23 (x y : ℝ) : 0 ≤ (845266860550 * x ^ 2 + 2 * (-282146938362) * x * y + 122489558390 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 845266860550 122489558390 (-282146938362)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc24 (x y : ℝ) : 0 ≤ (1778215931360 * x ^ 2 + 2 * (-578579785308) * x * y + 256297489880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1778215931360 256297489880 (-578579785308)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc25 (x y : ℝ) : 0 ≤ (2279143529040 * x ^ 2 + 2 * (-745978027176) * x * y + 372083389800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2279143529040 372083389800 (-745978027176)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc26 (x y : ℝ) : 0 ≤ (1788549165360 * x ^ 2 + 2 * (-602996442390) * x * y + 364816194000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1788549165360 364816194000 (-602996442390)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc27 (x y : ℝ) : 0 ≤ (812120570600 * x ^ 2 + 2 * (-287401557276) * x * y + 225136329320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 812120570600 225136329320 (-287401557276)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc28 (x y : ℝ) : 0 ≤ (180759057120 * x ^ 2 + 2 * (-68832498252) * x * y + 77525043680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 180759057120 77525043680 (-68832498252)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc29 (x y : ℝ) : 0 ≤ (11207911520 * x ^ 2 + 2 * (-5072000256) * x * y + 11177908960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 11207911520 11177908960 (-5072000256)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc30 (x y : ℝ) : 0 ≤ (57424677120 * x ^ 2 + 2 * (-18240186432) * x * y + 8752198440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 57424677120 8752198440 (-18240186432)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc31 (x y : ℝ) : 0 ≤ (427408481760 * x ^ 2 + 2 * (-121902009504) * x * y + 46960006840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 427408481760 46960006840 (-121902009504)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc32 (x y : ℝ) : 0 ≤ (1354979833680 * x ^ 2 + 2 * (-369635775972) * x * y + 132511404600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1354979833680 132511404600 (-369635775972)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc33 (x y : ℝ) : 0 ≤ (2335284584520 * x ^ 2 + 2 * (-644290848684) * x * y + 264455406040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2335284584520 264455406040 (-644290848684)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc34 (x y : ℝ) : 0 ≤ (2314380041840 * x ^ 2 + 2 * (-671796834156) * x * y + 361053363840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2314380041840 361053363840 (-671796834156)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc35 (x y : ℝ) : 0 ≤ (1273781484400 * x ^ 2 + 2 * (-399373018968) * x * y + 300412453200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1273781484400 300412453200 (-399373018968)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc36 (x y : ℝ) : 0 ≤ (332954019200 * x ^ 2 + 2 * (-115979530680) * x * y + 133372143040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 332954019200 133372143040 (-115979530680)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc37 (x y : ℝ) : 0 ≤ (23260046400 * x ^ 2 + 2 * (-10085577984) * x * y + 23861243840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 23260046400 23861243840 (-10085577984)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc38 (x y : ℝ) : 0 ≤ (77762971200 * x ^ 2 + 2 * (-17789831232) * x * y + 7541591760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 77762971200 7541591760 (-17789831232)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc39 (x y : ℝ) : 0 ≤ (493437357440 * x ^ 2 + 2 * (-101591457984) * x * y + 28214978720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 493437357440 28214978720 (-101591457984)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc40 (x y : ℝ) : 0 ≤ (1285576703920 * x ^ 2 + 2 * (-267283549584) * x * y + 74673287920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1285576703920 74673287920 (-267283549584)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc41 (x y : ℝ) : 0 ≤ (1718237028160 * x ^ 2 + 2 * (-391066386192) * x * y + 165890628160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1718237028160 165890628160 (-391066386192)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc42 (x y : ℝ) : 0 ≤ (1196224464480 * x ^ 2 + 2 * (-310896101904) * x * y + 214524771680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1196224464480 214524771680 (-310896101904)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc43 (x y : ℝ) : 0 ≤ (378170711680 * x ^ 2 + 2 * (-115836715344) * x * y + 133928609920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 378170711680 133928609920 (-115836715344)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc44 (x y : ℝ) : 0 ≤ (30228862080 * x ^ 2 + 2 * (-12498736896) * x * y + 31279050880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 30228862080 31279050880 (-12498736896)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc45 (x y : ℝ) : 0 ≤ (68316026880 * x ^ 2 + 2 * (-8488967808) * x * y + 3815876160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 68316026880 3815876160 (-8488967808)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc46 (x y : ℝ) : 0 ≤ (357444307200 * x ^ 2 + 2 * (-42153516672) * x * y + 5956595200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 357444307200 5956595200 (-42153516672)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc47 (x y : ℝ) : 0 ≤ (724822974400 * x ^ 2 + 2 * (-103067609184) * x * y + 24963448640 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 724822974400 24963448640 (-103067609184)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc48 (x y : ℝ) : 0 ≤ (681702796160 * x ^ 2 + 2 * (-127313018976) * x * y + 75229811840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 681702796160 75229811840 (-127313018976)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc49 (x y : ℝ) : 0 ≤ (271322538240 * x ^ 2 + 2 * (-67980349344) * x * y + 78316302080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 271322538240 78316302080 (-67980349344)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc50 (x y : ℝ) : 0 ≤ (25031959040 * x ^ 2 + 2 * (-9913962240) * x * y + 25833786880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 25031959040 25833786880 (-9913962240)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc51 (x y : ℝ) : 0 ≤ (38811640320 * x ^ 2 + 2 * (-95439360) * x * y + 1914585600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 38811640320 1914585600 (-95439360)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc52 (x y : ℝ) : 0 ≤ (158722022400 * x ^ 2 + 2 * (-3819116544) * x * y + 520084480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 158722022400 520084480 (-3819116544)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc53 (x y : ℝ) : 0 ≤ (226916362240 * x ^ 2 + 2 * (-18862228608) * x * y + 10060011520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 226916362240 10060011520 (-18862228608)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc54 (x y : ℝ) : 0 ≤ (120937564160 * x ^ 2 + 2 * (-20769705984) * x * y + 25004124160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 120937564160 25004124160 (-20769705984)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc55 (x y : ℝ) : 0 ≤ (12853027840 * x ^ 2 + 2 * (-4925164032) * x * y + 13148922880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 12853027840 13148922880 (-4925164032)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc56 (x y : ℝ) : 0 ≤ (13695129600 * x ^ 2 + 2 * 1846354944 * x * y + 1661306880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 13695129600 1661306880 1846354944
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc57 (x y : ℝ) : 0 ≤ (39557816320 * x ^ 2 + 2 * 2675395584 * x * y + 1792000000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 39557816320 1792000000 2675395584
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc58 (x y : ℝ) : 0 ≤ (31551016960 * x ^ 2 + 2 * (-1632589824) * x * y + 4175810560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 31551016960 4175810560 (-1632589824)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc59 (x y : ℝ) : 0 ≤ (3734077440 * x ^ 2 + 2 * (-1402601472) * x * y + 3776348160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3734077440 3776348160 (-1402601472)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc60 (x y : ℝ) : 0 ≤ (2713436160 * x ^ 2 + 2 * 744124416 * x * y + 998522880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2713436160 998522880 744124416
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc61 (x y : ℝ) : 0 ≤ (4254597120 * x ^ 2 + 2 * 586432512 * x * y + 824770560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4254597120 824770560 586432512
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc62 (x y : ℝ) : 0 ≤ (469401600 * x ^ 2 + 2 * (-175325184) * x * y + 469401600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 469401600 469401600 (-175325184)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_CBE_hc63 (x y : ℝ) : 0 ≤ (230031360 * x ^ 2 + 2 * 84639744 * x * y + 230031360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 230031360 230031360 84639744
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem B_CBE_entry11 (z w : ℝ) : 4423680 * Hdiag (1 + w / 2) ((1 + z) / 2) =
      801184320 * ((1 - z - w) ^ 10) +
      8562733920 * (w * (1 - z - w) ^ 9) +
      41306927990 * (w ^ 2 * (1 - z - w) ^ 8) +
      117734863255 * (w ^ 3 * (1 - z - w) ^ 7) +
      218089833145 * (w ^ 4 * (1 - z - w) ^ 6) +
      272150628440 * (w ^ 5 * (1 - z - w) ^ 5) +
      229268099560 * (w ^ 6 * (1 - z - w) ^ 4) +
      126700975140 * (w ^ 7 * (1 - z - w) ^ 3) +
      42696211500 * (w ^ 8 * (1 - z - w) ^ 2) +
      7406401920 * (w ^ 9 * (1 - z - w)) +
      393346160 * (w ^ 10) +
      7007873280 * (z * (1 - z - w) ^ 9) +
      67365565600 * (z * w * (1 - z - w) ^ 8) +
      288182431260 * (z * w ^ 2 * (1 - z - w) ^ 7) +
      714403928815 * (z * w ^ 3 * (1 - z - w) ^ 6) +
      1120635267720 * (z * w ^ 4 * (1 - z - w) ^ 5) +
      1140070612440 * (z * w ^ 5 * (1 - z - w) ^ 4) +
      739294413040 * (z * w ^ 6 * (1 - z - w) ^ 3) +
      285623877140 * (z * w ^ 7 * (1 - z - w) ^ 2) +
      55470434640 * (z * w ^ 8 * (1 - z - w)) +
      3126466320 * (z * w ^ 9) +
      26584506240 * (z ^ 2 * (1 - z - w) ^ 8) +
      226799460000 * (z ^ 2 * w * (1 - z - w) ^ 7) +
      845266860550 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 6) +
      1778215931360 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 5) +
      2279143529040 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 4) +
      1788549165360 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 3) +
      812120570600 * (z ^ 2 * w ^ 6 * (1 - z - w) ^ 2) +
      180759057120 * (z ^ 2 * w ^ 7 * (1 - z - w)) +
      11207911520 * (z ^ 2 * w ^ 8) +
      57424677120 * (z ^ 3 * (1 - z - w) ^ 7) +
      427408481760 * (z ^ 3 * w * (1 - z - w) ^ 6) +
      1354979833680 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 5) +
      2335284584520 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 4) +
      2314380041840 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 3) +
      1273781484400 * (z ^ 3 * w ^ 5 * (1 - z - w) ^ 2) +
      332954019200 * (z ^ 3 * w ^ 6 * (1 - z - w)) +
      23260046400 * (z ^ 3 * w ^ 7) +
      77762971200 * (z ^ 4 * (1 - z - w) ^ 6) +
      493437357440 * (z ^ 4 * w * (1 - z - w) ^ 5) +
      1285576703920 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 4) +
      1718237028160 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 3) +
      1196224464480 * (z ^ 4 * w ^ 4 * (1 - z - w) ^ 2) +
      378170711680 * (z ^ 4 * w ^ 5 * (1 - z - w)) +
      30228862080 * (z ^ 4 * w ^ 6) +
      68316026880 * (z ^ 5 * (1 - z - w) ^ 5) +
      357444307200 * (z ^ 5 * w * (1 - z - w) ^ 4) +
      724822974400 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 3) +
      681702796160 * (z ^ 5 * w ^ 3 * (1 - z - w) ^ 2) +
      271322538240 * (z ^ 5 * w ^ 4 * (1 - z - w)) +
      25031959040 * (z ^ 5 * w ^ 5) +
      38811640320 * (z ^ 6 * (1 - z - w) ^ 4) +
      158722022400 * (z ^ 6 * w * (1 - z - w) ^ 3) +
      226916362240 * (z ^ 6 * w ^ 2 * (1 - z - w) ^ 2) +
      120937564160 * (z ^ 6 * w ^ 3 * (1 - z - w)) +
      12853027840 * (z ^ 6 * w ^ 4) +
      13695129600 * (z ^ 7 * (1 - z - w) ^ 3) +
      39557816320 * (z ^ 7 * w * (1 - z - w) ^ 2) +
      31551016960 * (z ^ 7 * w ^ 2 * (1 - z - w)) +
      3734077440 * (z ^ 7 * w ^ 3) +
      2713436160 * (z ^ 8 * (1 - z - w) ^ 2) +
      4254597120 * (z ^ 8 * w * (1 - z - w)) +
      469401600 * (z ^ 8 * w ^ 2) +
      230031360 * (z ^ 9 * (1 - z - w)) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_CBE_entry22 (z w : ℝ) : 4423680 * Hdiag ((1 + z) / 2) (1 + w / 2) =
      268058655 * ((1 - z - w) ^ 10) +
      2424699900 * (w * (1 - z - w) ^ 9) +
      10173524930 * (w ^ 2 * (1 - z - w) ^ 8) +
      26323350300 * (w ^ 3 * (1 - z - w) ^ 7) +
      46666997155 * (w ^ 4 * (1 - z - w) ^ 6) +
      58940711680 * (w ^ 5 * (1 - z - w) ^ 5) +
      53082247440 * (w ^ 6 * (1 - z - w) ^ 4) +
      33154198640 * (w ^ 7 * (1 - z - w) ^ 3) +
      13529485940 * (w ^ 8 * (1 - z - w) ^ 2) +
      3206825040 * (w ^ 9 * (1 - z - w)) +
      329471440 * (w ^ 10) +
      1920065325 * (z * (1 - z - w) ^ 9) +
      15181140175 * (z * w * (1 - z - w) ^ 8) +
      56215690575 * (z * w ^ 2 * (1 - z - w) ^ 7) +
      130051701445 * (z * w ^ 3 * (1 - z - w) ^ 6) +
      207097920020 * (z * w ^ 4 * (1 - z - w) ^ 5) +
      231339973620 * (z * w ^ 5 * (1 - z - w) ^ 4) +
      176689548020 * (z * w ^ 6 * (1 - z - w) ^ 3) +
      86812409740 * (z * w ^ 7 * (1 - z - w) ^ 2) +
      24395377920 * (z * w ^ 8 * (1 - z - w)) +
      2933376880 * (z * w ^ 9) +
      5656719270 * (z ^ 2 * (1 - z - w) ^ 8) +
      37905178180 * (z ^ 2 * w * (1 - z - w) ^ 7) +
      122489558390 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 6) +
      256297489880 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 5) +
      372083389800 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 4) +
      364816194000 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 3) +
      225136329320 * (z ^ 2 * w ^ 6 * (1 - z - w) ^ 2) +
      77525043680 * (z ^ 2 * w ^ 7 * (1 - z - w)) +
      11177908960 * (z ^ 2 * w ^ 8) +
      8752198440 * (z ^ 3 * (1 - z - w) ^ 7) +
      46960006840 * (z ^ 3 * w * (1 - z - w) ^ 6) +
      132511404600 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 5) +
      264455406040 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 4) +
      361053363840 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 3) +
      300412453200 * (z ^ 3 * w ^ 5 * (1 - z - w) ^ 2) +
      133372143040 * (z ^ 3 * w ^ 6 * (1 - z - w)) +
      23861243840 * (z ^ 3 * w ^ 7) +
      7541591760 * (z ^ 4 * (1 - z - w) ^ 6) +
      28214978720 * (z ^ 4 * w * (1 - z - w) ^ 5) +
      74673287920 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 4) +
      165890628160 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 3) +
      214524771680 * (z ^ 4 * w ^ 4 * (1 - z - w) ^ 2) +
      133928609920 * (z ^ 4 * w ^ 5 * (1 - z - w)) +
      31279050880 * (z ^ 4 * w ^ 6) +
      3815876160 * (z ^ 5 * (1 - z - w) ^ 5) +
      5956595200 * (z ^ 5 * w * (1 - z - w) ^ 4) +
      24963448640 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 3) +
      75229811840 * (z ^ 5 * w ^ 3 * (1 - z - w) ^ 2) +
      78316302080 * (z ^ 5 * w ^ 4 * (1 - z - w)) +
      25833786880 * (z ^ 5 * w ^ 5) +
      1914585600 * (z ^ 6 * (1 - z - w) ^ 4) +
      520084480 * (z ^ 6 * w * (1 - z - w) ^ 3) +
      10060011520 * (z ^ 6 * w ^ 2 * (1 - z - w) ^ 2) +
      25004124160 * (z ^ 6 * w ^ 3 * (1 - z - w)) +
      13148922880 * (z ^ 6 * w ^ 4) +
      1661306880 * (z ^ 7 * (1 - z - w) ^ 3) +
      1792000000 * (z ^ 7 * w * (1 - z - w) ^ 2) +
      4175810560 * (z ^ 7 * w ^ 2 * (1 - z - w)) +
      3776348160 * (z ^ 7 * w ^ 3) +
      998522880 * (z ^ 8 * (1 - z - w) ^ 2) +
      824770560 * (z ^ 8 * w * (1 - z - w)) +
      469401600 * (z ^ 8 * w ^ 2) +
      230031360 * (z ^ 9 * (1 - z - w)) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_CBE_entry12 (z w : ℝ) : 4423680 * Hmixed (1 + w / 2) ((1 + z) / 2) =
      (-411481728) * ((1 - z - w) ^ 10) +
      (-4043672640) * (w * (1 - z - w) ^ 9) +
      (-18200711394) * (w ^ 2 * (1 - z - w) ^ 8) +
      (-49253308176) * (w ^ 3 * (1 - z - w) ^ 7) +
      (-88160628018) * (w ^ 4 * (1 - z - w) ^ 6) +
      (-108010148874) * (w ^ 5 * (1 - z - w) ^ 5) +
      (-90535912416) * (w ^ 6 * (1 - z - w) ^ 4) +
      (-50337642738) * (w ^ 7 * (1 - z - w) ^ 3) +
      (-17244612132) * (w ^ 8 * (1 - z - w) ^ 2) +
      (-3087266892) * (w ^ 9 * (1 - z - w)) +
      (-178693632) * (w ^ 10) +
      (-3209126976) * (z * (1 - z - w) ^ 9) +
      (-28132139808) * (z * w * (1 - z - w) ^ 8) +
      (-112332778152) * (z * w ^ 2 * (1 - z - w) ^ 7) +
      (-266661879312) * (z * w ^ 3 * (1 - z - w) ^ 6) +
      (-410215838064) * (z * w ^ 4 * (1 - z - w) ^ 5) +
      (-417500433960) * (z * w ^ 5 * (1 - z - w) ^ 4) +
      (-275202297480) * (z * w ^ 6 * (1 - z - w) ^ 3) +
      (-109649733144) * (z * w ^ 7 * (1 - z - w) ^ 2) +
      (-22431923856) * (z * w ^ 8 * (1 - z - w)) +
      (-1447778304) * (z * w ^ 9) +
      (-10454658624) * (z ^ 2 * (1 - z - w) ^ 8) +
      (-80644455744) * (z ^ 2 * w * (1 - z - w) ^ 7) +
      (-282146938362) * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 6) +
      (-578579785308) * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 5) +
      (-745978027176) * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 4) +
      (-602996442390) * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 3) +
      (-287401557276) * (z ^ 2 * w ^ 6 * (1 - z - w) ^ 2) +
      (-68832498252) * (z ^ 2 * w ^ 7 * (1 - z - w)) +
      (-5072000256) * (z ^ 2 * w ^ 8) +
      (-18240186432) * (z ^ 3 * (1 - z - w) ^ 7) +
      (-121902009504) * (z ^ 3 * w * (1 - z - w) ^ 6) +
      (-369635775972) * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 5) +
      (-644290848684) * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 4) +
      (-671796834156) * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 3) +
      (-399373018968) * (z ^ 3 * w ^ 5 * (1 - z - w) ^ 2) +
      (-115979530680) * (z ^ 3 * w ^ 6 * (1 - z - w)) +
      (-10085577984) * (z ^ 3 * w ^ 7) +
      (-17789831232) * (z ^ 4 * (1 - z - w) ^ 6) +
      (-101591457984) * (z ^ 4 * w * (1 - z - w) ^ 5) +
      (-267283549584) * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 4) +
      (-391066386192) * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 3) +
      (-310896101904) * (z ^ 4 * w ^ 4 * (1 - z - w) ^ 2) +
      (-115836715344) * (z ^ 4 * w ^ 5 * (1 - z - w)) +
      (-12498736896) * (z ^ 4 * w ^ 6) +
      (-8488967808) * (z ^ 5 * (1 - z - w) ^ 5) +
      (-42153516672) * (z ^ 5 * w * (1 - z - w) ^ 4) +
      (-103067609184) * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 3) +
      (-127313018976) * (z ^ 5 * w ^ 3 * (1 - z - w) ^ 2) +
      (-67980349344) * (z ^ 5 * w ^ 4 * (1 - z - w)) +
      (-9913962240) * (z ^ 5 * w ^ 5) +
      (-95439360) * (z ^ 6 * (1 - z - w) ^ 4) +
      (-3819116544) * (z ^ 6 * w * (1 - z - w) ^ 3) +
      (-18862228608) * (z ^ 6 * w ^ 2 * (1 - z - w) ^ 2) +
      (-20769705984) * (z ^ 6 * w ^ 3 * (1 - z - w)) +
      (-4925164032) * (z ^ 6 * w ^ 4) +
      1846354944 * (z ^ 7 * (1 - z - w) ^ 3) +
      2675395584 * (z ^ 7 * w * (1 - z - w) ^ 2) +
      (-1632589824) * (z ^ 7 * w ^ 2 * (1 - z - w)) +
      (-1402601472) * (z ^ 7 * w ^ 3) +
      744124416 * (z ^ 8 * (1 - z - w) ^ 2) +
      586432512 * (z ^ 8 * w * (1 - z - w)) +
      (-175325184) * (z ^ 8 * w ^ 2) +
      84639744 * (z ^ 9 * (1 - z - w)) := by
  simp only [Hmixed, mixedNumerator, Sbound, denominator, kappaB]
  ring
private def B_CBE_data (z w : ℝ) : List (ℝ × ℝ × ℝ × ℝ) :=
  [(801184320, 268058655, (-411481728), (1 - z - w) ^ 10),
  (8562733920, 2424699900, (-4043672640), w * (1 - z - w) ^ 9),
  (41306927990, 10173524930, (-18200711394), w ^ 2 * (1 - z - w) ^ 8),
  (117734863255, 26323350300, (-49253308176), w ^ 3 * (1 - z - w) ^ 7),
  (218089833145, 46666997155, (-88160628018), w ^ 4 * (1 - z - w) ^ 6),
  (272150628440, 58940711680, (-108010148874), w ^ 5 * (1 - z - w) ^ 5),
  (229268099560, 53082247440, (-90535912416), w ^ 6 * (1 - z - w) ^ 4),
  (126700975140, 33154198640, (-50337642738), w ^ 7 * (1 - z - w) ^ 3),
  (42696211500, 13529485940, (-17244612132), w ^ 8 * (1 - z - w) ^ 2),
  (7406401920, 3206825040, (-3087266892), w ^ 9 * (1 - z - w)),
  (393346160, 329471440, (-178693632), w ^ 10),
  (7007873280, 1920065325, (-3209126976), z * (1 - z - w) ^ 9),
  (67365565600, 15181140175, (-28132139808), z * w * (1 - z - w) ^ 8),
  (288182431260, 56215690575, (-112332778152), z * w ^ 2 * (1 - z - w) ^ 7),
  (714403928815, 130051701445, (-266661879312), z * w ^ 3 * (1 - z - w) ^ 6),
  (1120635267720, 207097920020, (-410215838064), z * w ^ 4 * (1 - z - w) ^ 5),
  (1140070612440, 231339973620, (-417500433960), z * w ^ 5 * (1 - z - w) ^ 4),
  (739294413040, 176689548020, (-275202297480), z * w ^ 6 * (1 - z - w) ^ 3),
  (285623877140, 86812409740, (-109649733144), z * w ^ 7 * (1 - z - w) ^ 2),
  (55470434640, 24395377920, (-22431923856), z * w ^ 8 * (1 - z - w)),
  (3126466320, 2933376880, (-1447778304), z * w ^ 9),
  (26584506240, 5656719270, (-10454658624), z ^ 2 * (1 - z - w) ^ 8),
  (226799460000, 37905178180, (-80644455744), z ^ 2 * w * (1 - z - w) ^ 7),
  (845266860550, 122489558390, (-282146938362), z ^ 2 * w ^ 2 * (1 - z - w) ^ 6),
  (1778215931360, 256297489880, (-578579785308), z ^ 2 * w ^ 3 * (1 - z - w) ^ 5),
  (2279143529040, 372083389800, (-745978027176), z ^ 2 * w ^ 4 * (1 - z - w) ^ 4),
  (1788549165360, 364816194000, (-602996442390), z ^ 2 * w ^ 5 * (1 - z - w) ^ 3),
  (812120570600, 225136329320, (-287401557276), z ^ 2 * w ^ 6 * (1 - z - w) ^ 2),
  (180759057120, 77525043680, (-68832498252), z ^ 2 * w ^ 7 * (1 - z - w)),
  (11207911520, 11177908960, (-5072000256), z ^ 2 * w ^ 8),
  (57424677120, 8752198440, (-18240186432), z ^ 3 * (1 - z - w) ^ 7),
  (427408481760, 46960006840, (-121902009504), z ^ 3 * w * (1 - z - w) ^ 6),
  (1354979833680, 132511404600, (-369635775972), z ^ 3 * w ^ 2 * (1 - z - w) ^ 5),
  (2335284584520, 264455406040, (-644290848684), z ^ 3 * w ^ 3 * (1 - z - w) ^ 4),
  (2314380041840, 361053363840, (-671796834156), z ^ 3 * w ^ 4 * (1 - z - w) ^ 3),
  (1273781484400, 300412453200, (-399373018968), z ^ 3 * w ^ 5 * (1 - z - w) ^ 2),
  (332954019200, 133372143040, (-115979530680), z ^ 3 * w ^ 6 * (1 - z - w)),
  (23260046400, 23861243840, (-10085577984), z ^ 3 * w ^ 7),
  (77762971200, 7541591760, (-17789831232), z ^ 4 * (1 - z - w) ^ 6),
  (493437357440, 28214978720, (-101591457984), z ^ 4 * w * (1 - z - w) ^ 5),
  (1285576703920, 74673287920, (-267283549584), z ^ 4 * w ^ 2 * (1 - z - w) ^ 4),
  (1718237028160, 165890628160, (-391066386192), z ^ 4 * w ^ 3 * (1 - z - w) ^ 3),
  (1196224464480, 214524771680, (-310896101904), z ^ 4 * w ^ 4 * (1 - z - w) ^ 2),
  (378170711680, 133928609920, (-115836715344), z ^ 4 * w ^ 5 * (1 - z - w)),
  (30228862080, 31279050880, (-12498736896), z ^ 4 * w ^ 6),
  (68316026880, 3815876160, (-8488967808), z ^ 5 * (1 - z - w) ^ 5),
  (357444307200, 5956595200, (-42153516672), z ^ 5 * w * (1 - z - w) ^ 4),
  (724822974400, 24963448640, (-103067609184), z ^ 5 * w ^ 2 * (1 - z - w) ^ 3),
  (681702796160, 75229811840, (-127313018976), z ^ 5 * w ^ 3 * (1 - z - w) ^ 2),
  (271322538240, 78316302080, (-67980349344), z ^ 5 * w ^ 4 * (1 - z - w)),
  (25031959040, 25833786880, (-9913962240), z ^ 5 * w ^ 5),
  (38811640320, 1914585600, (-95439360), z ^ 6 * (1 - z - w) ^ 4),
  (158722022400, 520084480, (-3819116544), z ^ 6 * w * (1 - z - w) ^ 3),
  (226916362240, 10060011520, (-18862228608), z ^ 6 * w ^ 2 * (1 - z - w) ^ 2),
  (120937564160, 25004124160, (-20769705984), z ^ 6 * w ^ 3 * (1 - z - w)),
  (12853027840, 13148922880, (-4925164032), z ^ 6 * w ^ 4),
  (13695129600, 1661306880, 1846354944, z ^ 7 * (1 - z - w) ^ 3),
  (39557816320, 1792000000, 2675395584, z ^ 7 * w * (1 - z - w) ^ 2),
  (31551016960, 4175810560, (-1632589824), z ^ 7 * w ^ 2 * (1 - z - w)),
  (3734077440, 3776348160, (-1402601472), z ^ 7 * w ^ 3),
  (2713436160, 998522880, 744124416, z ^ 8 * (1 - z - w) ^ 2),
  (4254597120, 824770560, 586432512, z ^ 8 * w * (1 - z - w)),
  (469401600, 469401600, (-175325184), z ^ 8 * w ^ 2),
  (230031360, 230031360, 84639744, z ^ 9 * (1 - z - w))]

private theorem B_CBE_entry11_list (z w : ℝ) :
    4423680 * Hdiag (1 + w / 2) ((1 + z) / 2) = ((B_CBE_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [B_CBE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_CBE_entry11 z w

private theorem B_CBE_entry22_list (z w : ℝ) :
    4423680 * Hdiag ((1 + z) / 2) (1 + w / 2) = ((B_CBE_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [B_CBE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_CBE_entry22 z w

private theorem B_CBE_entry12_list (z w : ℝ) :
    4423680 * Hmixed (1 + w / 2) ((1 + z) / 2) = ((B_CBE_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [B_CBE_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_CBE_entry12 z w

private theorem B_CBE {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ Hdiag (1 + w / 2) ((1 + z) / 2) * x ^ 2 + 2 * Hmixed (1 + w / 2) ((1 + z) / 2) * x * y + Hdiag ((1 + z) / 2) (1 + w / 2) * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (B_CBE_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (B_CBE_hc0 x y) (by positivity),
      mul_nonneg (B_CBE_hc1 x y) (by positivity),
      mul_nonneg (B_CBE_hc2 x y) (by positivity),
      mul_nonneg (B_CBE_hc3 x y) (by positivity),
      mul_nonneg (B_CBE_hc4 x y) (by positivity),
      mul_nonneg (B_CBE_hc5 x y) (by positivity),
      mul_nonneg (B_CBE_hc6 x y) (by positivity),
      mul_nonneg (B_CBE_hc7 x y) (by positivity),
      mul_nonneg (B_CBE_hc8 x y) (by positivity),
      mul_nonneg (B_CBE_hc9 x y) (by positivity),
      mul_nonneg (B_CBE_hc10 x y) (by positivity),
      mul_nonneg (B_CBE_hc11 x y) (by positivity),
      mul_nonneg (B_CBE_hc12 x y) (by positivity),
      mul_nonneg (B_CBE_hc13 x y) (by positivity),
      mul_nonneg (B_CBE_hc14 x y) (by positivity),
      mul_nonneg (B_CBE_hc15 x y) (by positivity),
      mul_nonneg (B_CBE_hc16 x y) (by positivity),
      mul_nonneg (B_CBE_hc17 x y) (by positivity),
      mul_nonneg (B_CBE_hc18 x y) (by positivity),
      mul_nonneg (B_CBE_hc19 x y) (by positivity),
      mul_nonneg (B_CBE_hc20 x y) (by positivity),
      mul_nonneg (B_CBE_hc21 x y) (by positivity),
      mul_nonneg (B_CBE_hc22 x y) (by positivity),
      mul_nonneg (B_CBE_hc23 x y) (by positivity),
      mul_nonneg (B_CBE_hc24 x y) (by positivity),
      mul_nonneg (B_CBE_hc25 x y) (by positivity),
      mul_nonneg (B_CBE_hc26 x y) (by positivity),
      mul_nonneg (B_CBE_hc27 x y) (by positivity),
      mul_nonneg (B_CBE_hc28 x y) (by positivity),
      mul_nonneg (B_CBE_hc29 x y) (by positivity),
      mul_nonneg (B_CBE_hc30 x y) (by positivity),
      mul_nonneg (B_CBE_hc31 x y) (by positivity),
      mul_nonneg (B_CBE_hc32 x y) (by positivity),
      mul_nonneg (B_CBE_hc33 x y) (by positivity),
      mul_nonneg (B_CBE_hc34 x y) (by positivity),
      mul_nonneg (B_CBE_hc35 x y) (by positivity),
      mul_nonneg (B_CBE_hc36 x y) (by positivity),
      mul_nonneg (B_CBE_hc37 x y) (by positivity),
      mul_nonneg (B_CBE_hc38 x y) (by positivity),
      mul_nonneg (B_CBE_hc39 x y) (by positivity),
      mul_nonneg (B_CBE_hc40 x y) (by positivity),
      mul_nonneg (B_CBE_hc41 x y) (by positivity),
      mul_nonneg (B_CBE_hc42 x y) (by positivity),
      mul_nonneg (B_CBE_hc43 x y) (by positivity),
      mul_nonneg (B_CBE_hc44 x y) (by positivity),
      mul_nonneg (B_CBE_hc45 x y) (by positivity),
      mul_nonneg (B_CBE_hc46 x y) (by positivity),
      mul_nonneg (B_CBE_hc47 x y) (by positivity),
      mul_nonneg (B_CBE_hc48 x y) (by positivity),
      mul_nonneg (B_CBE_hc49 x y) (by positivity),
      mul_nonneg (B_CBE_hc50 x y) (by positivity),
      mul_nonneg (B_CBE_hc51 x y) (by positivity),
      mul_nonneg (B_CBE_hc52 x y) (by positivity),
      mul_nonneg (B_CBE_hc53 x y) (by positivity),
      mul_nonneg (B_CBE_hc54 x y) (by positivity),
      mul_nonneg (B_CBE_hc55 x y) (by positivity),
      mul_nonneg (B_CBE_hc56 x y) (by positivity),
      mul_nonneg (B_CBE_hc57 x y) (by positivity),
      mul_nonneg (B_CBE_hc58 x y) (by positivity),
      mul_nonneg (B_CBE_hc59 x y) (by positivity),
      mul_nonneg (B_CBE_hc60 x y) (by positivity),
      mul_nonneg (B_CBE_hc61 x y) (by positivity),
      mul_nonneg (B_CBE_hc62 x y) (by positivity),
      mul_nonneg (B_CBE_hc63 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (B_CBE_data z w) x y hcoeff
  rw [← B_CBE_entry11_list, ← B_CBE_entry12_list, ← B_CBE_entry22_list] at hpos
  nlinarith only [hpos]

private theorem B_SUB_hc0 (x y : ℝ) : 0 ≤ (49168270 * x ^ 2 + 2 * (-22336704) * x * y + 41183930 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 49168270 41183930 (-22336704)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc1 (x y : ℝ) : 0 ≤ (543388840 * x ^ 2 + 2 * (-243425088) * x * y + 415822560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 543388840 415822560 (-243425088)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc2 (x y : ℝ) : 0 ≤ (2673339480 * x ^ 2 + 2 * (-1153680480) * x * y + 1794425480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 2673339480 1794425480 (-1153680480)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc3 (x y : ℝ) : 0 ≤ (7760123200 * x ^ 2 + 2 * (-3112849152) * x * y + 4314525920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7760123200 4314525920 (-3112849152)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc4 (x y : ℝ) : 0 ≤ (14806380960 * x ^ 2 + 2 * (-5245682976) * x * y + 6303251040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 14806380960 6303251040 (-5245682976)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc5 (x y : ℝ) : 0 ≤ (19443891840 * x ^ 2 + 2 * (-5679671040) * x * y + 5702181120 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 19443891840 5702181120 (-5679671040)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc6 (x y : ℝ) : 0 ≤ (17677765760 * x ^ 2 + 2 * (-3893891328) * x * y + 3095873920 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 17677765760 3095873920 (-3893891328)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc7 (x y : ℝ) : 0 ≤ (10734141440 * x ^ 2 + 2 * (-1583225856) * x * y + 913528320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 10734141440 913528320 (-1583225856)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc8 (x y : ℝ) : 0 ≤ (3931484160 * x ^ 2 + 2 * (-322748928) * x * y + 114227200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 3931484160 114227200 (-322748928)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc9 (x y : ℝ) : 0 ≤ (656629760 * x ^ 2 + 2 * (-19169280) * x * y + 2867200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 656629760 2867200 (-19169280)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc10 (x y : ℝ) : 0 ≤ (1411623920 * x ^ 2 + 2 * (-568507731) * x * y + 393850220 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1411623920 393850220 (-568507731)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc11 (x y : ℝ) : 0 ≤ (13273615880 * x ^ 2 + 2 * (-5483286111) * x * y + 3716574680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 13273615880 3716574680 (-5483286111)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc12 (x y : ℝ) : 0 ≤ (53824274400 * x ^ 2 + 2 * (-22430970468) * x * y + 14697336080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 53824274400 14697336080 (-22430970468)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc13 (x y : ℝ) : 0 ≤ (123134689280 * x ^ 2 + 2 * (-50644725144) * x * y + 31604568320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 123134689280 31604568320 (-50644725144)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc14 (x y : ℝ) : 0 ≤ (174270951680 * x ^ 2 + 2 * (-68544068208) * x * y + 40055151680 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 174270951680 40055151680 (-68544068208)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc15 (x y : ℝ) : 0 ≤ (156863665280 * x ^ 2 + 2 * (-56169060720) * x * y + 30163859840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 156863665280 30163859840 (-56169060720)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc16 (x y : ℝ) : 0 ≤ (88221780480 * x ^ 2 + 2 * (-26440593984) * x * y + 12790106880 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 88221780480 12790106880 (-26440593984)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc17 (x y : ℝ) : 0 ≤ (28595973120 * x ^ 2 + 2 * (-6077335296) * x * y + 2610508800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 28595973120 2610508800 (-6077335296)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc18 (x y : ℝ) : 0 ≤ (4140032000 * x ^ 2 + 2 * (-390266880) * x * y + 159129600 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4140032000 159129600 (-390266880)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc19 (x y : ℝ) : 0 ≤ (7469862110 * x ^ 2 + 2 * (-3079817403) * x * y + 1669286890 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 7469862110 1669286890 (-3079817403)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc20 (x y : ℝ) : 0 ≤ (60205371080 * x ^ 2 + 2 * (-25619389440) * x * y + 14032682720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 60205371080 14032682720 (-25619389440)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc21 (x y : ℝ) : 0 ≤ (203544223600 * x ^ 2 + 2 * (-87982309740) * x * y + 48056590480 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 203544223600 48056590480 (-87982309740)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc22 (x y : ℝ) : 0 ≤ (373399956320 * x ^ 2 + 2 * (-160643005848) * x * y + 86336007200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 373399956320 86336007200 (-160643005848)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc23 (x y : ℝ) : 0 ≤ (400157511840 * x ^ 2 + 2 * (-166234328256) * x * y + 86884020960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 400157511840 86884020960 (-166234328256)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc24 (x y : ℝ) : 0 ≤ (249290947840 * x ^ 2 + 2 * (-94812150432) * x * y + 47859667840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 249290947840 47859667840 (-94812150432)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc25 (x y : ℝ) : 0 ≤ (82949318400 * x ^ 2 + 2 * (-25713724800) * x * y + 12663558400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 82949318400 12663558400 (-25713724800)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc26 (x y : ℝ) : 0 ≤ (11227755520 * x ^ 2 + 2 * (-1935458304) * x * y + 1048238080 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 11227755520 1048238080 (-1935458304)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc27 (x y : ℝ) : 0 ≤ (18701432940 * x ^ 2 + 2 * (-8380386078) * x * y + 4477312320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 18701432940 4477312320 (-8380386078)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc28 (x y : ℝ) : 0 ≤ (125716400880 * x ^ 2 + 2 * (-57907053450) * x * y + 31599593360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 125716400880 31599593360 (-57907053450)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc29 (x y : ℝ) : 0 ≤ (341672107600 * x ^ 2 + 2 * (-159635026176) * x * y + 88142738800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 341672107600 88142738800 (-159635026176)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc30 (x y : ℝ) : 0 ≤ (476720688000 * x ^ 2 + 2 * (-221770504608) * x * y + 123060686720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 476720688000 123060686720 (-221770504608)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc31 (x y : ℝ) : 0 ≤ (355101402880 * x ^ 2 + 2 * (-159320425824) * x * y + 88912475840 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 355101402880 88912475840 (-159320425824)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc32 (x y : ℝ) : 0 ≤ (130187968000 * x ^ 2 + 2 * (-52398289248) * x * y + 30131228160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 130187968000 30131228160 (-52398289248)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc33 (x y : ℝ) : 0 ≤ (17145254400 * x ^ 2 + 2 * (-4728342528) * x * y + 3266539520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 17145254400 3266539520 (-4728342528)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc34 (x y : ℝ) : 0 ≤ (27140741400 * x ^ 2 + 2 * (-13757379354) * x * y + 8132644800 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 27140741400 8132644800 (-13757379354)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc35 (x y : ℝ) : 0 ≤ (146059566320 * x ^ 2 + 2 * (-75561729732) * x * y + 45703501360 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 146059566320 45703501360 (-75561729732)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc36 (x y : ℝ) : 0 ≤ (300518359280 * x ^ 2 + 2 * (-157336610328) * x * y + 97358206160 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 300518359280 97358206160 (-157336610328)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc37 (x y : ℝ) : 0 ≤ (289056963520 * x ^ 2 + 2 * (-150986683632) * x * y + 96381975040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 289056963520 96381975040 (-150986683632)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc38 (x y : ℝ) : 0 ≤ (123778866240 * x ^ 2 + 2 * (-62428893696) * x * y + 42621838400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 123778866240 42621838400 (-62428893696)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc39 (x y : ℝ) : 0 ≤ (16242622720 * x ^ 2 + 2 * (-6906190848) * x * y + 6034667520 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 16242622720 6034667520 (-6906190848)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc40 (x y : ℝ) : 0 ≤ (24392653680 * x ^ 2 + 2 * (-14312214684) * x * y + 9813151200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 24392653680 9813151200 (-14312214684)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc41 (x y : ℝ) : 0 ≤ (98710177600 * x ^ 2 + 2 * (-58990890096) * x * y + 41738952960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 98710177600 41738952960 (-58990890096)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc42 (x y : ℝ) : 0 ≤ (138513159520 * x ^ 2 + 2 * (-84419254128) * x * y + 62620629760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 138513159520 62620629760 (-84419254128)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc43 (x y : ℝ) : 0 ≤ (74496707200 * x ^ 2 + 2 * (-46499686656) * x * y + 37887058560 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 74496707200 37887058560 (-46499686656)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc44 (x y : ℝ) : 0 ≤ (9946865280 * x ^ 2 + 2 * (-6514311168) * x * y + 7120701440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 9946865280 7120701440 (-6514311168)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc45 (x y : ℝ) : 0 ≤ (13580183000 * x ^ 2 + 2 * (-9337286520) * x * y + 7571487400 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 13580183000 7571487400 (-9337286520)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc46 (x y : ℝ) : 0 ≤ (37110996800 * x ^ 2 + 2 * (-26376268896) * x * y + 22690404320 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 37110996800 22690404320 (-26376268896)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc47 (x y : ℝ) : 0 ≤ (28376274400 * x ^ 2 + 2 * (-21625075680) * x * y + 20857274720 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 28376274400 20857274720 (-21625075680)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc48 (x y : ℝ) : 0 ≤ (4029969280 * x ^ 2 + 2 * (-4056941568) * x * y + 5443379200 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4029969280 5443379200 (-4056941568)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc49 (x y : ℝ) : 0 ≤ (4394016400 * x ^ 2 + 2 * (-3585031680) * x * y + 3522363040 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 4394016400 3522363040 (-3585031680)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc50 (x y : ℝ) : 0 ≤ (6436015680 * x ^ 2 + 2 * (-5805189888) * x * y + 6506192960 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 6436015680 6506192960 (-5805189888)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc51 (x y : ℝ) : 0 ≤ (1115109440 * x ^ 2 + 2 * (-1628974080) * x * y + 2615101440 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 1115109440 2615101440 (-1628974080)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc52 (x y : ℝ) : 0 ≤ (683864320 * x ^ 2 + 2 * (-690057984) * x * y + 878089760 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 683864320 878089760 (-690057984)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc53 (x y : ℝ) : 0 ≤ (216320000 * x ^ 2 + 2 * (-384872448) * x * y + 718336000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 216320000 718336000 (-384872448)
      (by norm_num) (by norm_num) (by norm_num) x y


private theorem B_SUB_hc54 (x y : ℝ) : 0 ≤ (24092160 * x ^ 2 + 2 * (-40737792) * x * y + 86016000 * y ^ 2) := by
  exact quadratic_form_nonneg_of_det 24092160 86016000 (-40737792)
      (by norm_num) (by norm_num) (by norm_num) x y

private theorem B_SUB_entry11 (z w : ℝ) : 552960 * Hdiag ((3 - z + w) / 2) ((1 - z - w) / 2) =
      49168270 * ((1 - z - w) ^ 9) +
      543388840 * (w * (1 - z - w) ^ 8) +
      2673339480 * (w ^ 2 * (1 - z - w) ^ 7) +
      7760123200 * (w ^ 3 * (1 - z - w) ^ 6) +
      14806380960 * (w ^ 4 * (1 - z - w) ^ 5) +
      19443891840 * (w ^ 5 * (1 - z - w) ^ 4) +
      17677765760 * (w ^ 6 * (1 - z - w) ^ 3) +
      10734141440 * (w ^ 7 * (1 - z - w) ^ 2) +
      3931484160 * (w ^ 8 * (1 - z - w)) +
      656629760 * (w ^ 9) +
      1411623920 * (z * (1 - z - w) ^ 8) +
      13273615880 * (z * w * (1 - z - w) ^ 7) +
      53824274400 * (z * w ^ 2 * (1 - z - w) ^ 6) +
      123134689280 * (z * w ^ 3 * (1 - z - w) ^ 5) +
      174270951680 * (z * w ^ 4 * (1 - z - w) ^ 4) +
      156863665280 * (z * w ^ 5 * (1 - z - w) ^ 3) +
      88221780480 * (z * w ^ 6 * (1 - z - w) ^ 2) +
      28595973120 * (z * w ^ 7 * (1 - z - w)) +
      4140032000 * (z * w ^ 8) +
      7469862110 * (z ^ 2 * (1 - z - w) ^ 7) +
      60205371080 * (z ^ 2 * w * (1 - z - w) ^ 6) +
      203544223600 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      373399956320 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      400157511840 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      249290947840 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      82949318400 * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      11227755520 * (z ^ 2 * w ^ 7) +
      18701432940 * (z ^ 3 * (1 - z - w) ^ 6) +
      125716400880 * (z ^ 3 * w * (1 - z - w) ^ 5) +
      341672107600 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      476720688000 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      355101402880 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      130187968000 * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      17145254400 * (z ^ 3 * w ^ 6) +
      27140741400 * (z ^ 4 * (1 - z - w) ^ 5) +
      146059566320 * (z ^ 4 * w * (1 - z - w) ^ 4) +
      300518359280 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      289056963520 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      123778866240 * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      16242622720 * (z ^ 4 * w ^ 5) +
      24392653680 * (z ^ 5 * (1 - z - w) ^ 4) +
      98710177600 * (z ^ 5 * w * (1 - z - w) ^ 3) +
      138513159520 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      74496707200 * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      9946865280 * (z ^ 5 * w ^ 4) +
      13580183000 * (z ^ 6 * (1 - z - w) ^ 3) +
      37110996800 * (z ^ 6 * w * (1 - z - w) ^ 2) +
      28376274400 * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      4029969280 * (z ^ 6 * w ^ 3) +
      4394016400 * (z ^ 7 * (1 - z - w) ^ 2) +
      6436015680 * (z ^ 7 * w * (1 - z - w)) +
      1115109440 * (z ^ 7 * w ^ 2) +
      683864320 * (z ^ 8 * (1 - z - w)) +
      216320000 * (z ^ 8 * w) +
      24092160 * (z ^ 9) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_SUB_entry22 (z w : ℝ) : 552960 * Hdiag ((1 - z - w) / 2) ((3 - z + w) / 2) =
      41183930 * ((1 - z - w) ^ 9) +
      415822560 * (w * (1 - z - w) ^ 8) +
      1794425480 * (w ^ 2 * (1 - z - w) ^ 7) +
      4314525920 * (w ^ 3 * (1 - z - w) ^ 6) +
      6303251040 * (w ^ 4 * (1 - z - w) ^ 5) +
      5702181120 * (w ^ 5 * (1 - z - w) ^ 4) +
      3095873920 * (w ^ 6 * (1 - z - w) ^ 3) +
      913528320 * (w ^ 7 * (1 - z - w) ^ 2) +
      114227200 * (w ^ 8 * (1 - z - w)) +
      2867200 * (w ^ 9) +
      393850220 * (z * (1 - z - w) ^ 8) +
      3716574680 * (z * w * (1 - z - w) ^ 7) +
      14697336080 * (z * w ^ 2 * (1 - z - w) ^ 6) +
      31604568320 * (z * w ^ 3 * (1 - z - w) ^ 5) +
      40055151680 * (z * w ^ 4 * (1 - z - w) ^ 4) +
      30163859840 * (z * w ^ 5 * (1 - z - w) ^ 3) +
      12790106880 * (z * w ^ 6 * (1 - z - w) ^ 2) +
      2610508800 * (z * w ^ 7 * (1 - z - w)) +
      159129600 * (z * w ^ 8) +
      1669286890 * (z ^ 2 * (1 - z - w) ^ 7) +
      14032682720 * (z ^ 2 * w * (1 - z - w) ^ 6) +
      48056590480 * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      86336007200 * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      86884020960 * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      47859667840 * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      12663558400 * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      1048238080 * (z ^ 2 * w ^ 7) +
      4477312320 * (z ^ 3 * (1 - z - w) ^ 6) +
      31599593360 * (z ^ 3 * w * (1 - z - w) ^ 5) +
      88142738800 * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      123060686720 * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      88912475840 * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      30131228160 * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      3266539520 * (z ^ 3 * w ^ 6) +
      8132644800 * (z ^ 4 * (1 - z - w) ^ 5) +
      45703501360 * (z ^ 4 * w * (1 - z - w) ^ 4) +
      97358206160 * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      96381975040 * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      42621838400 * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      6034667520 * (z ^ 4 * w ^ 5) +
      9813151200 * (z ^ 5 * (1 - z - w) ^ 4) +
      41738952960 * (z ^ 5 * w * (1 - z - w) ^ 3) +
      62620629760 * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      37887058560 * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      7120701440 * (z ^ 5 * w ^ 4) +
      7571487400 * (z ^ 6 * (1 - z - w) ^ 3) +
      22690404320 * (z ^ 6 * w * (1 - z - w) ^ 2) +
      20857274720 * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      5443379200 * (z ^ 6 * w ^ 3) +
      3522363040 * (z ^ 7 * (1 - z - w) ^ 2) +
      6506192960 * (z ^ 7 * w * (1 - z - w)) +
      2615101440 * (z ^ 7 * w ^ 2) +
      878089760 * (z ^ 8 * (1 - z - w)) +
      718336000 * (z ^ 8 * w) +
      86016000 * (z ^ 9) := by
  simp only [Hdiag, denominator, radialDenominator, axialCoefficient, weight, theta, kappaV, kappa]
  ring

private theorem B_SUB_entry12 (z w : ℝ) : 552960 * Hmixed ((3 - z + w) / 2) ((1 - z - w) / 2) =
      (-22336704) * ((1 - z - w) ^ 9) +
      (-243425088) * (w * (1 - z - w) ^ 8) +
      (-1153680480) * (w ^ 2 * (1 - z - w) ^ 7) +
      (-3112849152) * (w ^ 3 * (1 - z - w) ^ 6) +
      (-5245682976) * (w ^ 4 * (1 - z - w) ^ 5) +
      (-5679671040) * (w ^ 5 * (1 - z - w) ^ 4) +
      (-3893891328) * (w ^ 6 * (1 - z - w) ^ 3) +
      (-1583225856) * (w ^ 7 * (1 - z - w) ^ 2) +
      (-322748928) * (w ^ 8 * (1 - z - w)) +
      (-19169280) * (w ^ 9) +
      (-568507731) * (z * (1 - z - w) ^ 8) +
      (-5483286111) * (z * w * (1 - z - w) ^ 7) +
      (-22430970468) * (z * w ^ 2 * (1 - z - w) ^ 6) +
      (-50644725144) * (z * w ^ 3 * (1 - z - w) ^ 5) +
      (-68544068208) * (z * w ^ 4 * (1 - z - w) ^ 4) +
      (-56169060720) * (z * w ^ 5 * (1 - z - w) ^ 3) +
      (-26440593984) * (z * w ^ 6 * (1 - z - w) ^ 2) +
      (-6077335296) * (z * w ^ 7 * (1 - z - w)) +
      (-390266880) * (z * w ^ 8) +
      (-3079817403) * (z ^ 2 * (1 - z - w) ^ 7) +
      (-25619389440) * (z ^ 2 * w * (1 - z - w) ^ 6) +
      (-87982309740) * (z ^ 2 * w ^ 2 * (1 - z - w) ^ 5) +
      (-160643005848) * (z ^ 2 * w ^ 3 * (1 - z - w) ^ 4) +
      (-166234328256) * (z ^ 2 * w ^ 4 * (1 - z - w) ^ 3) +
      (-94812150432) * (z ^ 2 * w ^ 5 * (1 - z - w) ^ 2) +
      (-25713724800) * (z ^ 2 * w ^ 6 * (1 - z - w)) +
      (-1935458304) * (z ^ 2 * w ^ 7) +
      (-8380386078) * (z ^ 3 * (1 - z - w) ^ 6) +
      (-57907053450) * (z ^ 3 * w * (1 - z - w) ^ 5) +
      (-159635026176) * (z ^ 3 * w ^ 2 * (1 - z - w) ^ 4) +
      (-221770504608) * (z ^ 3 * w ^ 3 * (1 - z - w) ^ 3) +
      (-159320425824) * (z ^ 3 * w ^ 4 * (1 - z - w) ^ 2) +
      (-52398289248) * (z ^ 3 * w ^ 5 * (1 - z - w)) +
      (-4728342528) * (z ^ 3 * w ^ 6) +
      (-13757379354) * (z ^ 4 * (1 - z - w) ^ 5) +
      (-75561729732) * (z ^ 4 * w * (1 - z - w) ^ 4) +
      (-157336610328) * (z ^ 4 * w ^ 2 * (1 - z - w) ^ 3) +
      (-150986683632) * (z ^ 4 * w ^ 3 * (1 - z - w) ^ 2) +
      (-62428893696) * (z ^ 4 * w ^ 4 * (1 - z - w)) +
      (-6906190848) * (z ^ 4 * w ^ 5) +
      (-14312214684) * (z ^ 5 * (1 - z - w) ^ 4) +
      (-58990890096) * (z ^ 5 * w * (1 - z - w) ^ 3) +
      (-84419254128) * (z ^ 5 * w ^ 2 * (1 - z - w) ^ 2) +
      (-46499686656) * (z ^ 5 * w ^ 3 * (1 - z - w)) +
      (-6514311168) * (z ^ 5 * w ^ 4) +
      (-9337286520) * (z ^ 6 * (1 - z - w) ^ 3) +
      (-26376268896) * (z ^ 6 * w * (1 - z - w) ^ 2) +
      (-21625075680) * (z ^ 6 * w ^ 2 * (1 - z - w)) +
      (-4056941568) * (z ^ 6 * w ^ 3) +
      (-3585031680) * (z ^ 7 * (1 - z - w) ^ 2) +
      (-5805189888) * (z ^ 7 * w * (1 - z - w)) +
      (-1628974080) * (z ^ 7 * w ^ 2) +
      (-690057984) * (z ^ 8 * (1 - z - w)) +
      (-384872448) * (z ^ 8 * w) +
      (-40737792) * (z ^ 9) := by
  simp only [Hmixed, mixedNumerator, Sbound, denominator, kappaB]
  ring
private def B_SUB_data (z w : ℝ) : List (ℝ × ℝ × ℝ × ℝ) :=
  [(49168270, 41183930, (-22336704), (1 - z - w) ^ 9),
  (543388840, 415822560, (-243425088), w * (1 - z - w) ^ 8),
  (2673339480, 1794425480, (-1153680480), w ^ 2 * (1 - z - w) ^ 7),
  (7760123200, 4314525920, (-3112849152), w ^ 3 * (1 - z - w) ^ 6),
  (14806380960, 6303251040, (-5245682976), w ^ 4 * (1 - z - w) ^ 5),
  (19443891840, 5702181120, (-5679671040), w ^ 5 * (1 - z - w) ^ 4),
  (17677765760, 3095873920, (-3893891328), w ^ 6 * (1 - z - w) ^ 3),
  (10734141440, 913528320, (-1583225856), w ^ 7 * (1 - z - w) ^ 2),
  (3931484160, 114227200, (-322748928), w ^ 8 * (1 - z - w)),
  (656629760, 2867200, (-19169280), w ^ 9),
  (1411623920, 393850220, (-568507731), z * (1 - z - w) ^ 8),
  (13273615880, 3716574680, (-5483286111), z * w * (1 - z - w) ^ 7),
  (53824274400, 14697336080, (-22430970468), z * w ^ 2 * (1 - z - w) ^ 6),
  (123134689280, 31604568320, (-50644725144), z * w ^ 3 * (1 - z - w) ^ 5),
  (174270951680, 40055151680, (-68544068208), z * w ^ 4 * (1 - z - w) ^ 4),
  (156863665280, 30163859840, (-56169060720), z * w ^ 5 * (1 - z - w) ^ 3),
  (88221780480, 12790106880, (-26440593984), z * w ^ 6 * (1 - z - w) ^ 2),
  (28595973120, 2610508800, (-6077335296), z * w ^ 7 * (1 - z - w)),
  (4140032000, 159129600, (-390266880), z * w ^ 8),
  (7469862110, 1669286890, (-3079817403), z ^ 2 * (1 - z - w) ^ 7),
  (60205371080, 14032682720, (-25619389440), z ^ 2 * w * (1 - z - w) ^ 6),
  (203544223600, 48056590480, (-87982309740), z ^ 2 * w ^ 2 * (1 - z - w) ^ 5),
  (373399956320, 86336007200, (-160643005848), z ^ 2 * w ^ 3 * (1 - z - w) ^ 4),
  (400157511840, 86884020960, (-166234328256), z ^ 2 * w ^ 4 * (1 - z - w) ^ 3),
  (249290947840, 47859667840, (-94812150432), z ^ 2 * w ^ 5 * (1 - z - w) ^ 2),
  (82949318400, 12663558400, (-25713724800), z ^ 2 * w ^ 6 * (1 - z - w)),
  (11227755520, 1048238080, (-1935458304), z ^ 2 * w ^ 7),
  (18701432940, 4477312320, (-8380386078), z ^ 3 * (1 - z - w) ^ 6),
  (125716400880, 31599593360, (-57907053450), z ^ 3 * w * (1 - z - w) ^ 5),
  (341672107600, 88142738800, (-159635026176), z ^ 3 * w ^ 2 * (1 - z - w) ^ 4),
  (476720688000, 123060686720, (-221770504608), z ^ 3 * w ^ 3 * (1 - z - w) ^ 3),
  (355101402880, 88912475840, (-159320425824), z ^ 3 * w ^ 4 * (1 - z - w) ^ 2),
  (130187968000, 30131228160, (-52398289248), z ^ 3 * w ^ 5 * (1 - z - w)),
  (17145254400, 3266539520, (-4728342528), z ^ 3 * w ^ 6),
  (27140741400, 8132644800, (-13757379354), z ^ 4 * (1 - z - w) ^ 5),
  (146059566320, 45703501360, (-75561729732), z ^ 4 * w * (1 - z - w) ^ 4),
  (300518359280, 97358206160, (-157336610328), z ^ 4 * w ^ 2 * (1 - z - w) ^ 3),
  (289056963520, 96381975040, (-150986683632), z ^ 4 * w ^ 3 * (1 - z - w) ^ 2),
  (123778866240, 42621838400, (-62428893696), z ^ 4 * w ^ 4 * (1 - z - w)),
  (16242622720, 6034667520, (-6906190848), z ^ 4 * w ^ 5),
  (24392653680, 9813151200, (-14312214684), z ^ 5 * (1 - z - w) ^ 4),
  (98710177600, 41738952960, (-58990890096), z ^ 5 * w * (1 - z - w) ^ 3),
  (138513159520, 62620629760, (-84419254128), z ^ 5 * w ^ 2 * (1 - z - w) ^ 2),
  (74496707200, 37887058560, (-46499686656), z ^ 5 * w ^ 3 * (1 - z - w)),
  (9946865280, 7120701440, (-6514311168), z ^ 5 * w ^ 4),
  (13580183000, 7571487400, (-9337286520), z ^ 6 * (1 - z - w) ^ 3),
  (37110996800, 22690404320, (-26376268896), z ^ 6 * w * (1 - z - w) ^ 2),
  (28376274400, 20857274720, (-21625075680), z ^ 6 * w ^ 2 * (1 - z - w)),
  (4029969280, 5443379200, (-4056941568), z ^ 6 * w ^ 3),
  (4394016400, 3522363040, (-3585031680), z ^ 7 * (1 - z - w) ^ 2),
  (6436015680, 6506192960, (-5805189888), z ^ 7 * w * (1 - z - w)),
  (1115109440, 2615101440, (-1628974080), z ^ 7 * w ^ 2),
  (683864320, 878089760, (-690057984), z ^ 8 * (1 - z - w)),
  (216320000, 718336000, (-384872448), z ^ 8 * w),
  (24092160, 86016000, (-40737792), z ^ 9)]

private theorem B_SUB_entry11_list (z w : ℝ) :
    552960 * Hdiag ((3 - z + w) / 2) ((1 - z - w) / 2) = ((B_SUB_data z w).map (fun a => a.1 * a.2.2.2)).sum := by
  simpa only [B_SUB_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_SUB_entry11 z w

private theorem B_SUB_entry22_list (z w : ℝ) :
    552960 * Hdiag ((1 - z - w) / 2) ((3 - z + w) / 2) = ((B_SUB_data z w).map (fun a => a.2.1 * a.2.2.2)).sum := by
  simpa only [B_SUB_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_SUB_entry22 z w

private theorem B_SUB_entry12_list (z w : ℝ) :
    552960 * Hmixed ((3 - z + w) / 2) ((1 - z - w) / 2) = ((B_SUB_data z w).map (fun a => a.2.2.1 * a.2.2.2)).sum := by
  simpa only [B_SUB_data, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    zero_mul, zero_add, add_zero, add_assoc] using B_SUB_entry12 z w

private theorem B_SUB {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ Hdiag ((3 - z + w) / 2) ((1 - z - w) / 2) * x ^ 2 + 2 * Hmixed ((3 - z + w) / 2) ((1 - z - w) / 2) * x * y + Hdiag ((1 - z - w) / 2) ((3 - z + w) / 2) * y ^ 2 := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcoeff : (B_SUB_data z w).Forall
      (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2) := by
    exact ⟨mul_nonneg (B_SUB_hc0 x y) (by positivity),
      mul_nonneg (B_SUB_hc1 x y) (by positivity),
      mul_nonneg (B_SUB_hc2 x y) (by positivity),
      mul_nonneg (B_SUB_hc3 x y) (by positivity),
      mul_nonneg (B_SUB_hc4 x y) (by positivity),
      mul_nonneg (B_SUB_hc5 x y) (by positivity),
      mul_nonneg (B_SUB_hc6 x y) (by positivity),
      mul_nonneg (B_SUB_hc7 x y) (by positivity),
      mul_nonneg (B_SUB_hc8 x y) (by positivity),
      mul_nonneg (B_SUB_hc9 x y) (by positivity),
      mul_nonneg (B_SUB_hc10 x y) (by positivity),
      mul_nonneg (B_SUB_hc11 x y) (by positivity),
      mul_nonneg (B_SUB_hc12 x y) (by positivity),
      mul_nonneg (B_SUB_hc13 x y) (by positivity),
      mul_nonneg (B_SUB_hc14 x y) (by positivity),
      mul_nonneg (B_SUB_hc15 x y) (by positivity),
      mul_nonneg (B_SUB_hc16 x y) (by positivity),
      mul_nonneg (B_SUB_hc17 x y) (by positivity),
      mul_nonneg (B_SUB_hc18 x y) (by positivity),
      mul_nonneg (B_SUB_hc19 x y) (by positivity),
      mul_nonneg (B_SUB_hc20 x y) (by positivity),
      mul_nonneg (B_SUB_hc21 x y) (by positivity),
      mul_nonneg (B_SUB_hc22 x y) (by positivity),
      mul_nonneg (B_SUB_hc23 x y) (by positivity),
      mul_nonneg (B_SUB_hc24 x y) (by positivity),
      mul_nonneg (B_SUB_hc25 x y) (by positivity),
      mul_nonneg (B_SUB_hc26 x y) (by positivity),
      mul_nonneg (B_SUB_hc27 x y) (by positivity),
      mul_nonneg (B_SUB_hc28 x y) (by positivity),
      mul_nonneg (B_SUB_hc29 x y) (by positivity),
      mul_nonneg (B_SUB_hc30 x y) (by positivity),
      mul_nonneg (B_SUB_hc31 x y) (by positivity),
      mul_nonneg (B_SUB_hc32 x y) (by positivity),
      mul_nonneg (B_SUB_hc33 x y) (by positivity),
      mul_nonneg (B_SUB_hc34 x y) (by positivity),
      mul_nonneg (B_SUB_hc35 x y) (by positivity),
      mul_nonneg (B_SUB_hc36 x y) (by positivity),
      mul_nonneg (B_SUB_hc37 x y) (by positivity),
      mul_nonneg (B_SUB_hc38 x y) (by positivity),
      mul_nonneg (B_SUB_hc39 x y) (by positivity),
      mul_nonneg (B_SUB_hc40 x y) (by positivity),
      mul_nonneg (B_SUB_hc41 x y) (by positivity),
      mul_nonneg (B_SUB_hc42 x y) (by positivity),
      mul_nonneg (B_SUB_hc43 x y) (by positivity),
      mul_nonneg (B_SUB_hc44 x y) (by positivity),
      mul_nonneg (B_SUB_hc45 x y) (by positivity),
      mul_nonneg (B_SUB_hc46 x y) (by positivity),
      mul_nonneg (B_SUB_hc47 x y) (by positivity),
      mul_nonneg (B_SUB_hc48 x y) (by positivity),
      mul_nonneg (B_SUB_hc49 x y) (by positivity),
      mul_nonneg (B_SUB_hc50 x y) (by positivity),
      mul_nonneg (B_SUB_hc51 x y) (by positivity),
      mul_nonneg (B_SUB_hc52 x y) (by positivity),
      mul_nonneg (B_SUB_hc53 x y) (by positivity),
      mul_nonneg (B_SUB_hc54 x y) (by positivity)⟩
  have hpos := combine_quadratic_nonneg (B_SUB_data z w) x y hcoeff
  rw [← B_SUB_entry11_list, ← B_SUB_entry12_list, ← B_SUB_entry22_list] at hpos
  nlinarith only [hpos]

/-- The second matrix certificate, on the ordered half of the closed spectral
triangle. The six Bernstein triangles retain their boundary zero matrices. -/
theorem coupling_matrix_nonneg {v b : ℝ}
    (hb : 0 ≤ b) (horder : b ≤ v) (hsum : v + b ≤ 2) (x y : ℝ) :
    0 ≤ Hdiag v b * x ^ 2 + 2 * Hmixed v b * x * y + Hdiag b v * y ^ 2 := by
  by_cases hsmall : v + b ≤ 1
  · have h := B_OAS (z := 2 * b) (w := v - b) (by linarith) (by linarith)
      (by linarith) x y
    have hvrep : (2 * b) / 2 + (v - b) = v := by ring
    have hbrep : (2 * b) / 2 = b := by ring
    simpa only [hvrep, hbrep, show b + (v - b) = v by ring] using h
  · by_cases hv1 : v ≤ 1
    · by_cases hbhalf : b ≤ 1 / 2
      · have h := B_ASE (z := 2 * (1 - v)) (w := 1 - 2 * b) (by linarith) (by linarith)
          (by linarith) x y
        have hvrep : 1 - (2 * (1 - v)) / 2 = v := by ring
        have hbrep : (1 - (1 - 2 * b)) / 2 = b := by ring
        simpa only [hvrep, hbrep] using h
      · have h := B_ACE (z := 2 * (1 - v)) (w := 2 * b - 1) (by linarith) (by linarith)
          (by linarith) x y
        have hvrep : 1 - (2 * (1 - v)) / 2 = v := by ring
        have hbrep : (1 + (2 * b - 1)) / 2 = b := by ring
        simpa only [hvrep, hbrep] using h
    · by_cases hbhalf : b ≤ 1 / 2
      · by_cases hdiag : v - b ≤ 1
        · have h := B_SBE (z := 1 - 2 * b) (w := 2 * (v - 1)) (by linarith) (by linarith)
            (by linarith) x y
          have hvrep : 1 + (2 * (v - 1)) / 2 = v := by ring
          have hbrep : (1 - (1 - 2 * b)) / 2 = b := by ring
          simpa only [hvrep, hbrep] using h
        · have h := B_SUB (z := 2 - v - b) (w := v - b - 1) (by linarith) (by linarith)
            (by linarith) x y
          have hvrep : (3 - (2 - v - b) + (v - b - 1)) / 2 = v := by ring
          have hbrep : (1 - (2 - v - b) - (v - b - 1)) / 2 = b := by ring
          simpa only [hvrep, hbrep] using h
      · have h := B_CBE (z := 2 * b - 1) (w := 2 * (v - 1)) (by linarith) (by linarith)
          (by linarith) x y
        have hvrep : 1 + (2 * (v - 1)) / 2 = v := by ring
        have hbrep : (1 + (2 * b - 1)) / 2 = b := by ring
        simpa only [hvrep, hbrep] using h

end

end PositiveEinsteinFour.Quadratic
end


section

/-! The quadratic coupling bound (22), derived from the finite matrix certificate. -/

namespace PositiveEinsteinFour.Quadratic

open Potential

noncomputable section

def quadraticCoefficient (v b : ℝ) : ℝ :=
  axialCoefficient v b + 158 / denominator v b + kappaV v b + 2 * kappa v b / (3 * v)

def mixedCoefficient (v b : ℝ) : ℝ :=
  (kappaB v b + kappaB b v) / 2 - 158 / denominator v b

def diagonalDifference (v b : ℝ) : ℝ :=
  2 * theta v b * normWeight v - quadraticCoefficient v b

private theorem denominator_pos (v b : ℝ) : 0 < denominator v b := by
  unfold denominator
  positivity

private theorem radialDenominator_pos {v : ℝ} (hv : 0 ≤ v) :
    0 < radialDenominator v := by
  unfold radialDenominator
  positivity

private theorem denominator_swap (v b : ℝ) : denominator b v = denominator v b := by
  unfold denominator
  ring

private theorem diagonalDifference_eq {v b : ℝ} (hv : 0 < v) :
    diagonalDifference v b = Hdiag v b / (v * denominator v b * radialDenominator v) := by
  have hK := denominator_pos v b
  have hr := radialDenominator_pos hv.le
  unfold diagonalDifference quadraticCoefficient normWeight Hdiag
  unfold denominator radialDenominator at *
  field_simp
  ring

private theorem mixedCoefficient_eq (v b : ℝ) :
    mixedCoefficient v b = mixedNumerator v b / denominator v b := by
  have hK := denominator_pos v b
  unfold mixedCoefficient mixedNumerator
  field_simp

private theorem Sbound_sq (v b : ℝ) :
    v * b * radialDenominator v * radialDenominator b ≤ Sbound v b ^ 2 := by
  have hid : Sbound v b ^ 2 - v * b * radialDenominator v * radialDenominator b =
      ((5 / 4) * b * radialDenominator v - (4 / 5) * v * radialDenominator b) ^ 2 / 4 := by
    unfold Sbound radialDenominator
    ring
  have hnonneg : 0 ≤
      ((5 / 4) * b * radialDenominator v - (4 / 5) * v * radialDenominator b) ^ 2 / 4 := by
    positivity
  linarith

private theorem quotient_matrix_nonneg {v b : ℝ}
    (hv : 0 < v) (hb : 0 < b) (horder : b ≤ v) (hsum : v + b ≤ 2) (x y : ℝ) :
    0 ≤ (Hdiag v b / (v * denominator v b * radialDenominator v)) * x ^ 2 -
      2 * (mixedNumerator v b / denominator v b) * x * y +
      (Hdiag b v / (b * denominator v b * radialDenominator b)) * y ^ 2 := by
  obtain ⟨hH1, hH2, hdet⟩ := quadratic_form_det_of_nonneg
    (Hdiag v b) (Hdiag b v) (Hmixed v b)
    (coupling_matrix_nonneg hb.le horder hsum)
  have hK := denominator_pos v b
  have hrv := radialDenominator_pos hv.le
  have hrb := radialDenominator_pos hb.le
  have hd1 : 0 < v * denominator v b * radialDenominator v := by positivity
  have hd2 : 0 < b * denominator v b * radialDenominator b := by positivity
  have hcore : (v * b * radialDenominator v * radialDenominator b) *
      mixedNumerator v b ^ 2 ≤ Hdiag v b * Hdiag b v := by
    calc
      _ ≤ Sbound v b ^ 2 * mixedNumerator v b ^ 2 :=
        mul_le_mul_of_nonneg_right (Sbound_sq v b) (sq_nonneg _)
      _ = Hmixed v b ^ 2 := by unfold Hmixed; ring
      _ ≤ _ := hdet
  have hdet' : (mixedNumerator v b / denominator v b) ^ 2 ≤
      (Hdiag v b / (v * denominator v b * radialDenominator v)) *
      (Hdiag b v / (b * denominator v b * radialDenominator b)) := by
    rw [div_mul_div_comm]
    apply (le_div_iff₀ (mul_pos hd1 hd2)).2
    have hid : (mixedNumerator v b / denominator v b) ^ 2 *
        ((v * denominator v b * radialDenominator v) *
          (b * denominator v b * radialDenominator b)) =
        (v * b * radialDenominator v * radialDenominator b) * mixedNumerator v b ^ 2 := by
      field_simp
    rwa [hid]
  have h := quadratic_form_nonneg_of_det
    (Hdiag v b / (v * denominator v b * radialDenominator v))
    (Hdiag b v / (b * denominator v b * radialDenominator b))
    (-(mixedNumerator v b / denominator v b))
    (div_nonneg hH1 hd1.le) (div_nonneg hH2 hd2.le)
    (by simpa only [neg_sq] using hdet') x y
  nlinarith only [h]

private theorem ordered_quadratic_bound {v b : ℝ}
    (hv : 0 < v) (hb : 0 < b) (horder : b ≤ v) (hsum : v + b ≤ 2) (x y : ℝ) :
    quadraticCoefficient v b * x ^ 2 + 2 * mixedCoefficient v b * x * y +
      quadraticCoefficient b v * y ^ 2 ≤
      2 * theta v b * (normWeight v * x ^ 2 + normWeight b * y ^ 2) := by
  have h := quotient_matrix_nonneg hv hb horder hsum x y
  rw [← diagonalDifference_eq hv] at h
  rw [← denominator_swap v b, ← diagonalDifference_eq hb, denominator_swap v b,
    ← mixedCoefficient_eq] at h
  unfold diagonalDifference at h
  rw [Boundary.theta_swap v b] at h
  nlinarith only [h]

/-- The scalar quadratic-form inequality (22) on the positive part of the
spectral triangle. The result is symmetric, although its finite certificate
was verified on the half with the first block larger. -/
theorem quadratic_bound {v b : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hsum : v + b ≤ 2) (x y : ℝ) :
    quadraticCoefficient v b * x ^ 2 + 2 * mixedCoefficient v b * x * y +
      quadraticCoefficient b v * y ^ 2 ≤
      2 * theta v b * (normWeight v * x ^ 2 + normWeight b * y ^ 2) := by
  rcases le_total b v with horder | horder
  · exact ordered_quadratic_bound hv hb horder hsum x y
  · have h := ordered_quadratic_bound hb hv horder (by linarith) y x
    rw [Boundary.theta_swap v b] at h
    have hmid : mixedCoefficient b v = mixedCoefficient v b := by
      unfold mixedCoefficient
      rw [denominator_swap]
      ring
    rw [hmid] at h
    nlinarith only [h]

private theorem zero_second_diagonal_bound {v : ℝ} (hv : 0 < v) (hv2 : v ≤ 2) (x : ℝ) :
    quadraticCoefficient v 0 * x ^ 2 ≤ 2 * theta v 0 * normWeight v * x ^ 2 := by
  have h := coupling_matrix_nonneg (v := v) (b := 0) (by norm_num) hv.le (by simpa) 1 0
  have hH : 0 ≤ Hdiag v 0 := by simpa using h
  have hd : 0 ≤ diagonalDifference v 0 := by
    rw [diagonalDifference_eq hv]
    exact div_nonneg hH (by
      exact le_of_lt (mul_pos (mul_pos hv (denominator_pos v 0))
        (radialDenominator_pos hv.le)))
  have hm := mul_nonneg hd (sq_nonneg x)
  unfold diagonalDifference at hm
  nlinarith only [hm]

/-- Equation (22) on the closed spectral triangle, using the zero-set
convention that derivative entries vanish with their Weyl norm. No continuity
of a coefficient containing `1/v` or `1/b` is asserted. -/
theorem quadratic_bound_closed {v b : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hsum : v + b ≤ 2) (x y : ℝ)
    (hx : v = 0 → x = 0) (hy : b = 0 → y = 0) :
    quadraticCoefficient v b * x ^ 2 + 2 * mixedCoefficient v b * x * y +
      quadraticCoefficient b v * y ^ 2 ≤
      2 * theta v b * (normWeight v * x ^ 2 + normWeight b * y ^ 2) := by
  rcases eq_or_lt_of_le hv with hv0 | hvpos
  · have hvzero : v = 0 := hv0.symm
    subst v
    have hxzero := hx rfl
    subst x
    rcases eq_or_lt_of_le hb with hb0 | hbpos
    · have hbzero : b = 0 := hb0.symm
      subst b
      have hyzero := hy rfl
      subst y
      simp
    · have h := zero_second_diagonal_bound hbpos (by simpa using hsum) y
      rw [Boundary.theta_swap 0 b] at h
      simpa [mul_assoc] using h
  · rcases eq_or_lt_of_le hb with hb0 | hbpos
    · have hbzero : b = 0 := hb0.symm
      subst b
      have hyzero := hy rfl
      subst y
      have h := zero_second_diagonal_bound hvpos (by simpa using hsum) x
      simpa [mul_assoc] using h
    · exact quadratic_bound hvpos hbpos hsum x y

end

end PositiveEinsteinFour.Quadratic
end


section

/-!
# Assembly of the scalar integrand bounds

The quartic, quadratic, and potential estimates bound the scalar integrand.
The tangent pairing is the real inner product.
-/

namespace PositiveEinsteinFour

open Energy QuarticEnergy QuarticClosed Quadratic Boundary Potential

noncomputable section

/-- The scalar quadratic estimate also holds for tangent vectors, with their
actual pairing. The proof chooses the sign of a scalar test vector according
to the sign of the mixed coefficient. -/
theorem hilbert_quadratic_bound_closed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v b : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b) (hsum : v + b ≤ 2)
    (p q : E) (hp : v = 0 → p = 0) (hq : b = 0 → q = 0) :
    quadraticCoefficient v b * ‖p‖ ^ 2 + 2 * mixedCoefficient v b * inner ℝ p q +
      quadraticCoefficient b v * ‖q‖ ^ 2 ≤
      2 * theta v b * (normWeight v * ‖p‖ ^ 2 + normWeight b * ‖q‖ ^ 2) := by
  have habs := abs_real_inner_le_norm p q
  have hlo := (abs_le.mp habs).1
  have hhi := (abs_le.mp habs).2
  by_cases hJ : 0 ≤ mixedCoefficient v b
  · have hscalar := quadratic_bound_closed hv hb hsum ‖p‖ ‖q‖
      (by intro h; simp [hp h]) (by intro h; simp [hq h])
    have hcross := mul_le_mul_of_nonneg_left hhi
      (show 0 ≤ 2 * mixedCoefficient v b by positivity)
    nlinarith only [hscalar, hcross]
  · have hscalar := quadratic_bound_closed hv hb hsum ‖p‖ (-‖q‖)
      (by intro h; simp [hp h]) (by intro h; simp [hq h])
    have hcross := mul_le_mul_of_nonpos_left hlo
      (show 2 * mixedCoefficient v b ≤ 0 by linarith)
    nlinarith only [hscalar, hcross]

/-- The explicit upper expression obtained after the quartic projection and
quadratic axial reductions. It retains the two actual total derivative
energies and the inner product of the two norm gradients. -/
def reducedIntegrand
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v b r s σ τ ρ χ e f : ℝ) (p q : E) : ℝ :=
  quarticEnergy v b ((5 / 3) * ‖p‖ ^ 2) ((5 / 3) * ‖q‖ ^ 2)
      (projectionCoefficient v (b * s) σ ρ) (projectionCoefficient b (v * r) τ χ)
      (defectCoefficient v (b * s)) (defectCoefficient b (v * r)) e f +
    (quadraticCoefficient v b * ‖p‖ ^ 2 + 2 * mixedCoefficient v b * inner ℝ p q +
      quadraticCoefficient b v * ‖q‖ ^ 2) +
    zeroOrderIntegrand v b σ τ

/-- Every scalar estimate needed for the final coupled bound, including all
zero sets, follows from the concrete polynomial certificates. -/
theorem reduced_integrand_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v b r s σ τ ρ χ e f : ℝ} (p q : E)
    (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hr : 1 ≤ r) (hr2 : r ≤ 2) (hs : 1 ≤ s) (hs2 : s ≤ 2)
    (hspectral : v * r + b * s ≤ 2)
    (hσ : σ = (3 * r - r ^ 3) / 2) (hρ : ρ ^ 2 = 1 - σ ^ 2)
    (hτ : τ = (3 * s - s ^ 3) / 2) (hχ : χ ^ 2 = 1 - τ ^ 2)
    (he : (5 / 3) * ‖p‖ ^ 2 ≤ e) (hf : (5 / 3) * ‖q‖ ^ 2 ≤ f)
    (hve : v = 0 → e = 0) (hbf : b = 0 → f = 0) :
    reducedIntegrand v b r s σ τ ρ χ e f p q ≤
      -couplingCoefficient v b * (‖p‖ ^ 2 + ‖q‖ ^ 2) *
        (‖p‖ ^ 2 / v + ‖q‖ ^ 2 / b) +
      2 * theta v b * (normWeight v * ‖p‖ ^ 2 + normWeight b * ‖q‖ ^ 2) -
      theta v b ^ 2 / couplingCoefficient v b := by
  have hvx : v ≤ v * r := by nlinarith
  have hby : b ≤ b * s := by nlinarith
  have hsum : v + b ≤ 2 := by linarith
  have hpzero : v = 0 → p = 0 := by
    intro h
    have hn : ‖p‖ = 0 := by nlinarith [hve h, norm_nonneg p, sq_nonneg ‖p‖]
    exact norm_eq_zero.mp hn
  have hqzero : b = 0 → q = 0 := by
    intro h
    have hn : ‖q‖ = 0 := by nlinarith [hbf h, norm_nonneg q, sq_nonneg ‖q‖]
    exact norm_eq_zero.mp hn
  have h4 := quartic_energy_bound_closed hv hb hr hr2 hs hs2 hspectral hσ hρ hτ hχ
    (sq_nonneg ‖p‖) (sq_nonneg ‖q‖) he hf hve hbf
  have hc : 2 / 5 - 3 * v * b / 10 = couplingCoefficient v b := by
    unfold couplingCoefficient
    ring
  rw [hc] at h4
  have h2 := hilbert_quadratic_bound_closed hv hb hsum p q hpzero hqzero
  have hσupper : σ ≤ 1 := by
    have hfac : 1 - σ = (r - 1) ^ 2 * (r + 2) / 2 := by rw [hσ]; ring
    have hh : 0 ≤ (r - 1) ^ 2 * (r + 2) / 2 := by positivity
    linarith
  have hτupper : τ ≤ 1 := by
    have hfac : 1 - τ = (s - 1) ^ 2 * (s + 2) / 2 := by rw [hτ]; ring
    have hh : 0 ≤ (s - 1) ^ 2 * (s + 2) / 2 := by positivity
    linarith
  have hδ : 0 ≤ 2 - v - b := by linarith
  have hvdefect := spectral_potential_defect_bound hv hr hr2 hδ (by linarith) hσ
  have hbdefect := spectral_potential_defect_bound hb hs hs2 hδ (by linarith) hτ
  have h0 := zeroOrder_bound hv hb hsum hσupper hτupper hvdefect hbdefect
  unfold reducedIntegrand
  convert add_le_add (add_le_add h4 h2) h0 using 1
  ring

end
end PositiveEinsteinFour
end

end OAI
