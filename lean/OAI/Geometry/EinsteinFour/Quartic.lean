import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace OAI

/-!
# Scalar certificates for the quartic comparison

Exact rational signs for equation (20) and Lemma 7.2 of the manuscript.
The Bernstein expansions give exact rational coefficients and their signs.
-/

namespace PositiveEinsteinFour.Quartic

noncomputable section

def A (u : ℝ) : ℝ :=
  (67 / 50) * u ^ 2 + (67 / 50)

def G (u : ℝ) : ℝ :=
  (-9 / 800) * u ^ 4 + (-9 / 32) * u ^ 3 + (2889 / 3200) * u ^ 2 + (99 / 64) * u + (117 / 128)

def H (u : ℝ) : ℝ :=
  (315 / 512) * u ^ 4 + (243 / 256) * u ^ 3 + (2889 / 3200) * u ^ 2 + (81 / 256) * u + (3681 / 12800)

def L (u : ℝ) : ℝ :=
  (381 / 256) * u ^ 4 + (285 / 128) * u ^ 3 + (531 / 256) * u ^ 2 + (219 / 64) * u + (267 / 128)

def Z (u : ℝ) : ℝ := L u ^ 2 - 4 * A u * (G u + u ^ 2 * H u)

def discriminant (u : ℝ) : ℝ :=
  64 * A u ^ 2 * u ^ 2 * G u * H u - Z u ^ 2

theorem coefficients_as_in_manuscript (u : ℝ) :
    A u = (67 / 50) * (1 + u ^ 2) ∧
    G u = (27 / 100) * (1 + u ^ 2) * u ^ 2 +
      3 * (27 / 128) * (1 + u) ^ 2 + (9 / 32) * (1 + u) * (1 - u ^ 3) ∧
    H u = (27 / 100) * (1 + u ^ 2) +
      (27 / 128) * (17 + 19 * u ^ 2) * (1 + u) ^ 2 / 12 -
      (9 / 32) * (1 + u) * (1 - u ^ 3) ∧
    L u = (27 / 128) * (1 + u) ^ 2 * (19 / 3 + 7 * u ^ 2 / 2) +
      (3 / 4) * (1 + u) * (1 + u ^ 3) := by
  unfold A G H L
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem G_lower {u : ℝ} (hlo : 0 ≤ u) (hhi : u ≤ 1) :
    9 / 10 ≤ G u := by
  have hz : 0 ≤ ((u - 0) / 1) := by linarith
  have hw : 0 ≤ 1 - ((u - 0) / 1) := by linarith
  have hcert : 3200 * (G u - 9 / 10) =
      45 * (1 - ((u - 0) / 1)) ^ 4 +
      5130 * ((u - 0) / 1) * (1 - ((u - 0) / 1)) ^ 3 +
      18009 * ((u - 0) / 1) ^ 2 * (1 - ((u - 0) / 1)) ^ 2 +
      19908 * ((u - 0) / 1) ^ 3 * (1 - ((u - 0) / 1)) +
      6948 * ((u - 0) / 1) ^ 4 := by
    unfold G
    ring
  have hp : 0 ≤ 3200 * (G u - 9 / 10) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

theorem H_lower {u : ℝ} (hlo : 0 ≤ u) (hhi : u ≤ 1) :
    1 / 4 ≤ H u := by
  have hz : 0 ≤ ((u - 0) / 1) := by linarith
  have hw : 0 ≤ 1 - ((u - 0) / 1) := by linarith
  have hcert : 12800 * (H u - 1 / 4) =
      481 * (1 - ((u - 0) / 1)) ^ 4 +
      5974 * ((u - 0) / 1) * (1 - ((u - 0) / 1)) ^ 3 +
      26592 * ((u - 0) / 1) ^ 2 * (1 - ((u - 0) / 1)) ^ 2 +
      49336 * ((u - 0) / 1) ^ 3 * (1 - ((u - 0) / 1)) +
      36112 * ((u - 0) / 1) ^ 4 := by
    unfold H
    ring
  have hp : 0 ≤ 12800 * (H u - 1 / 4) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

theorem Z_nonpos_small {u : ℝ} (hlo : 0 ≤ u) (hhi : u ≤ (1 / 16)) :
    Z u ≤ 0 := by
  have hz : 0 ≤ ((u - 0) / (1 / 16)) := by linarith
  have hw : 0 ≤ 1 - ((u - 0) / (1 / 16)) := by linarith
  have hcert : 175921860444160000 * (-Z u) =
      96447356102246400 * (1 - ((u - 0) / (1 / 16))) ^ 8 +
      705779842469068800 * ((u - 0) / (1 / 16)) * (1 - ((u - 0) / (1 / 16))) ^ 7 +
      2233691314254249984 * ((u - 0) / (1 / 16)) ^ 2 * (1 - ((u - 0) / (1 / 16))) ^ 6 +
      3981178688979861504 * ((u - 0) / (1 / 16)) ^ 3 * (1 - ((u - 0) / (1 / 16))) ^ 5 +
      4351464125411033088 * ((u - 0) / (1 / 16)) ^ 4 * (1 - ((u - 0) / (1 / 16))) ^ 4 +
      2966650978945646592 * ((u - 0) / (1 / 16)) ^ 5 * (1 - ((u - 0) / (1 / 16))) ^ 3 +
      1218436049307151872 * ((u - 0) / (1 / 16)) ^ 6 * (1 - ((u - 0) / (1 / 16))) ^ 2 +
      270150054573127104 * ((u - 0) / (1 / 16)) ^ 7 * (1 - ((u - 0) / (1 / 16))) +
      23720719937369031 * ((u - 0) / (1 / 16)) ^ 8 := by
    unfold Z L A G H
    ring
  have hp : 0 ≤ 175921860444160000 * (-Z u) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

theorem discriminant_nonneg {u : ℝ} (hlo : (1 / 16) ≤ u) (hhi : u ≤ 1) :
    0 ≤ discriminant u := by
  have hz : 0 ≤ ((u - (1 / 16)) / (15 / 16)) := by linarith
  have hw : 0 ≤ 1 - ((u - (1 / 16)) / (15 / 16)) := by linarith
  have hcert : 49517601571415210995964968960000 * (discriminant u) =
      6168574436959761676638843427263 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 16 +
      424154777452262164887934458457728 * ((u - (1 / 16)) / (15 / 16)) * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 15 +
      5745102856303709684919706005519360 * ((u - (1 / 16)) / (15 / 16)) ^ 2 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 14 +
      39024793730224628563705435309178880 * ((u - (1 / 16)) / (15 / 16)) ^ 3 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 13 +
      166503926549188231049624719485173760 * ((u - (1 / 16)) / (15 / 16)) ^ 4 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 12 +
      495120111132825129677055074274115584 * ((u - (1 / 16)) / (15 / 16)) ^ 5 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 11 +
      1095446172671702946521384982794993664 * ((u - (1 / 16)) / (15 / 16)) ^ 6 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 10 +
      1906132635982707314500534987464376320 * ((u - (1 / 16)) / (15 / 16)) ^ 7 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 9 +
      2763874657831845070490101698275573760 * ((u - (1 / 16)) / (15 / 16)) ^ 8 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 8 +
      3521116051815405437512553791928401920 * ((u - (1 / 16)) / (15 / 16)) ^ 9 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 7 +
      4016512417947710025750779579496136704 * ((u - (1 / 16)) / (15 / 16)) ^ 10 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 6 +
      3969034635025022417002617853490233344 * ((u - (1 / 16)) / (15 / 16)) ^ 11 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 5 +
      3184400848861595859007882321157160960 * ((u - (1 / 16)) / (15 / 16)) ^ 12 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 4 +
      1930552432251624252702533599761530880 * ((u - (1 / 16)) / (15 / 16)) ^ 13 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 3 +
      815949494369681637713395413323612160 * ((u - (1 / 16)) / (15 / 16)) ^ 14 * (1 - ((u - (1 / 16)) / (15 / 16))) ^ 2 +
      212811373474353171256131286632235008 * ((u - (1 / 16)) / (15 / 16)) ^ 15 * (1 - ((u - (1 / 16)) / (15 / 16))) +
      25756730625900971793653188849041408 * ((u - (1 / 16)) / (15 / 16)) ^ 16 := by
    unfold discriminant Z L A G H
    ring
  have hp : 0 ≤ 49517601571415210995964968960000 * (discriminant u) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem sqrt_comparison {a g h l u : ℝ}
    (ha : 0 ≤ a) (hg : 0 ≤ g) (hh : 0 ≤ h) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hz : l ^ 2 - 4 * a * (g + u ^ 2 * h) ≤
      8 * a * u * Real.sqrt g * Real.sqrt h) :
    l ≤ 2 * Real.sqrt a * (Real.sqrt g + u * Real.sqrt h) := by
  have ht : 0 ≤ 2 * Real.sqrt a * (Real.sqrt g + u * Real.sqrt h) := by positivity
  have heq : (2 * Real.sqrt a * (Real.sqrt g + u * Real.sqrt h)) ^ 2 =
      4 * a * (g + u ^ 2 * h) + 8 * a * u * Real.sqrt g * Real.sqrt h := by
    calc
      _ = 4 * (Real.sqrt a) ^ 2 *
          ((Real.sqrt g) ^ 2 + u ^ 2 * (Real.sqrt h) ^ 2 +
            2 * u * Real.sqrt g * Real.sqrt h) := by ring
      _ = _ := by rw [Real.sq_sqrt ha, Real.sq_sqrt hg, Real.sq_sqrt hh]; ring
  apply (sq_le_sq₀ hl ht).mp
  rw [heq]
  linarith

/-- The square-root comparison deduced from the two discriminant certificates. -/
theorem root_bound {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    L u ≤ 2 * Real.sqrt (A u) * (Real.sqrt (G u) + u * Real.sqrt (H u)) := by
  have ha : 0 ≤ A u := by unfold A; positivity
  have hg : 0 ≤ G u := le_trans (by norm_num) (G_lower hu hu1)
  have hh : 0 ≤ H u := le_trans (by norm_num) (H_lower hu hu1)
  have hl : 0 ≤ L u := by unfold L; positivity
  apply sqrt_comparison ha hg hh hl hu
  change Z u ≤ 8 * A u * u * Real.sqrt (G u) * Real.sqrt (H u)
  by_cases hsmall : u ≤ 1 / 16
  · exact (Z_nonpos_small hu hsmall).trans (by positivity)
  · have hd := discriminant_nonneg (le_of_lt (lt_of_not_ge hsmall)) hu1
    unfold discriminant at hd
    have hk : 0 ≤ 8 * A u * u * Real.sqrt (G u) * Real.sqrt (H u) := by positivity
    have hksq : (8 * A u * u * Real.sqrt (G u) * Real.sqrt (H u)) ^ 2 =
        64 * A u ^ 2 * u ^ 2 * G u * H u := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hg, Real.sq_sqrt hh]
      ring
    have hs : (Z u) ^ 2 ≤
        (8 * A u * u * Real.sqrt (G u) * Real.sqrt (H u)) ^ 2 := by
      rw [hksq]
      linarith
    exact le_trans (le_abs_self _) ((sq_le_sq₀ (abs_nonneg _) hk).mp (by simpa using hs))

private theorem quotient_amgm {a g v : ℝ} (ha : 0 ≤ a) (hg : 0 ≤ g) (hv : 0 < v) :
    2 * Real.sqrt (a * g) ≤ a / v + g * v := by
  have hx : 0 ≤ a / v := div_nonneg ha hv.le
  have hy : 0 ≤ g * v := mul_nonneg hg hv.le
  have hprod : a / v * (g * v) = a * g := by field_simp
  have heq : Real.sqrt (a / v) * Real.sqrt (g * v) = Real.sqrt (a * g) := by
    rw [← Real.sqrt_mul hx, hprod]
  have hsq := sq_nonneg (Real.sqrt (a / v) - Real.sqrt (g * v))
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  nlinarith

/-- The relaxed quartic difference after division by `v b P⁴` is nonnegative.
This is the final arithmetic-geometric-mean step in equation (20). -/
theorem relaxed_quartic_nonneg {u v b : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 < v) (hb : 0 < b) :
    0 ≤ A u / v + A u * u ^ 2 / b + G u * v + H u * b - L u := by
  have ha : 0 ≤ A u := by unfold A; positivity
  have hg : 0 ≤ G u := le_trans (by norm_num) (G_lower hu hu1)
  have hh : 0 ≤ H u := le_trans (by norm_num) (H_lower hu hu1)
  have hamgm1 := quotient_amgm ha hg hv
  have hamgm2 := quotient_amgm (mul_nonneg ha (sq_nonneg u)) hh hb
  have hs1 : Real.sqrt (A u * G u) = Real.sqrt (A u) * Real.sqrt (G u) :=
    Real.sqrt_mul ha _
  have hs2 : Real.sqrt (A u * u ^ 2 * H u) =
      u * Real.sqrt (A u) * Real.sqrt (H u) := by
    rw [show A u * u ^ 2 * H u = u ^ 2 * (A u * H u) by ring,
      Real.sqrt_mul (sq_nonneg u), Real.sqrt_sq hu, Real.sqrt_mul ha]
    ring
  rw [hs1] at hamgm1
  rw [hs2] at hamgm2
  have hroot := root_bound hu hu1
  nlinarith

/-- Equation (20) after normalizing the larger gradient parameter to one
and enlarging the spectral defects to `(δ, 0)`, exactly as in the paper. -/
theorem enlarged_quartic_bound {u v b : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 < v) (hb : 0 < b) :
    (27 / 128) * v * b * (1 + u) ^ 2 *
        ((19 / 3 - 3 * v - 17 * b / 12) + (7 / 2 - 19 * b / 12) * u ^ 2) +
      (3 / 4) * v * b * (1 + u) *
        ((1 - 3 * (v - b) / 8) + (1 - 3 * (b - v) / 8) * u ^ 3) ≤
      (67 / 50 + 27 * v * b / 100) * (1 + u ^ 2) * (b + v * u ^ 2) := by
  have hp := mul_nonneg (mul_pos hv hb).le (relaxed_quartic_nonneg hu hu1 hv hb)
  have hid :
      (67 / 50 + 27 * v * b / 100) * (1 + u ^ 2) * (b + v * u ^ 2) -
        ((27 / 128) * v * b * (1 + u) ^ 2 *
          ((19 / 3 - 3 * v - 17 * b / 12) + (7 / 2 - 19 * b / 12) * u ^ 2) +
          (3 / 4) * v * b * (1 + u) *
            ((1 - 3 * (v - b) / 8) + (1 - 3 * (b - v) / 8) * u ^ 3)) =
      v * b * (A u / v + A u * u ^ 2 / b + G u * v + H u * b - L u) := by
    unfold A G H L
    field_simp
    ring
  rw [← hid] at hp
  linarith

private theorem spectral_polynomial_nonneg {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) :
    0 ≤ 4 * r * (r + 3) - (r - 1) * (r + 2) * (r + 1) ^ 2 := by
  have hz : 0 ≤ r - 1 := by linarith
  have hz1 : 0 ≤ 1 - (r - 1) := by linarith
  have hcert : 4 * r * (r + 3) - (r - 1) * (r + 2) * (r + 1) ^ 2 =
      16 * (1 - (r - 1)) ^ 4 + 72 * (r - 1) * (1 - (r - 1)) ^ 3 +
      108 * (r - 1) ^ 2 * (1 - (r - 1)) ^ 2 +
      57 * (r - 1) ^ 3 * (1 - (r - 1)) + 4 * (r - 1) ^ 4 := by ring
  rw [hcert]
  positivity

/-- The spectral-shape term in the quartic projection cost is bounded by
twice the minimum-eigenvalue defect. This keeps the cubic invariant of the
normalized trace-free block, instead of assuming an axial eigenvalue shape. -/
theorem spectral_defect_bound {v r σ ρ : ℝ}
    (hv : 0 ≤ v) (hr : 1 ≤ r) (hr2 : r ≤ 2) (hvr : v * r ≤ 2)
    (hσ : σ = (3 * r - r ^ 3) / 2) (hρ : ρ ^ 2 = 1 - σ ^ 2) :
    -σ * v + ρ ^ 2 * v ^ 2 / 4 ≤ -v + 2 * (v * r - v) := by
  have hp := spectral_polynomial_nonneg hr hr2
  have hrpos : 0 < r := by linarith
  have hplus : 1 + σ = (2 - r) * (r + 1) ^ 2 / 2 := by rw [hσ]; ring
  have hminus : 1 - σ = (r - 1) ^ 2 * (r + 2) / 2 := by rw [hσ]; ring
  have hplus_nonneg : 0 ≤ 1 + σ := by rw [hplus]; positivity
  have hprod1 := mul_nonneg (show 0 ≤ 2 - r by linarith) hp
  have hprod2 := mul_nonneg (show 0 ≤ 2 - r * v by nlinarith)
    (mul_nonneg (mul_nonneg (show 0 ≤ r - 1 by linarith)
      (show 0 ≤ r + 2 by linarith)) hplus_nonneg)
  have hid :
      8 * r * (2 - (r - 1) * (r + 2) / 2 * (1 + v * (1 + σ) / 4)) =
      (2 - r) * (4 * r * (r + 3) - (r - 1) * (r + 2) * (r + 1) ^ 2) +
        (2 - r * v) * (r - 1) * (r + 2) * (1 + σ) := by
    rw [hσ]
    ring
  have hbound : (r - 1) * (r + 2) / 2 * (1 + v * (1 + σ) / 4) ≤ 2 := by
    have hnonneg : 0 ≤ 8 * r *
        (2 - (r - 1) * (r + 2) / 2 * (1 + v * (1 + σ) / 4)) := by
      rw [hid]
      nlinarith
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hbound
    (mul_nonneg hv (show 0 ≤ r - 1 by linarith))
  have hshape :
      v * (r - 1) * ((r - 1) * (r + 2) / 2 * (1 + v * (1 + σ) / 4)) =
        v * (1 - σ) * (1 + v * (1 + σ) / 4) := by rw [hminus]; ring
  rw [hshape] at hmul
  rw [hρ]
  nlinarith

/-- The upper bound for the projection coefficient after introducing the
nonnegative spectral defects `V = x-v` and `W = y-b`. -/
def projectionBound (v b V W : ℝ) : ℝ :=
  (7 / 12) * (4 + b + W) - v + 2 * V

/-- The difference between the two sides of the paper's equation (20). -/
def quarticMargin (v b V W P Q : ℝ) : ℝ :=
  (67 / 50 + 27 * v * b / 100) * (P ^ 2 + Q ^ 2) * (b * P ^ 2 + v * Q ^ 2) -
    ((27 / 128) * v * b * (P + Q) ^ 2 *
        (projectionBound v b V W * P ^ 2 + projectionBound b v W V * Q ^ 2) +
      (3 / 4) * v * b * (P + Q) *
        ((1 - 3 * (v - b) / 8) * P ^ 3 + (1 - 3 * (b - v) / 8) * Q ^ 3))

private theorem projection_enlargement {u v b V W : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hW : 0 ≤ W) (hsum : V + W ≤ 2 - v - b) :
    projectionBound v b V W + projectionBound b v W V * u ^ 2 ≤
      (19 / 3 - 3 * v - 17 * b / 12) + (7 / 2 - 19 * b / 12) * u ^ 2 := by
  have hsquare : 0 ≤ 1 - u ^ 2 := by nlinarith
  have hterm1 := mul_nonneg hsquare hW
  have hterm2 := mul_nonneg (show 0 ≤ 2 + (7 / 12 : ℝ) * u ^ 2 by positivity)
    (show 0 ≤ 2 - v - b - V - W by linarith)
  unfold projectionBound
  nlinarith

private theorem normalized_margin_nonneg {u v b V W : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 < v) (hb : 0 < b)
    (hW : 0 ≤ W) (hsum : V + W ≤ 2 - v - b) :
    0 ≤ quarticMargin v b V W 1 u := by
  have hlarge := enlarged_quartic_bound hu hu1 hv hb
  have hproj := projection_enlargement hu hu1 hW hsum
  have hmul := mul_le_mul_of_nonneg_left hproj
    (show 0 ≤ (27 / 128 : ℝ) * v * b * (1 + u) ^ 2 by positivity)
  unfold quarticMargin
  norm_num only [one_pow, mul_one]
  linarith

theorem quarticMargin_swap (v b V W P Q : ℝ) :
    quarticMargin b v W V Q P = quarticMargin v b V W P Q := by
  unfold quarticMargin projectionBound
  ring

private theorem ordered_margin_nonneg {v b V W P Q : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hW : 0 ≤ W)
    (hsum : V + W ≤ 2 - v - b) (hP : 0 < P) (hQ : 0 ≤ Q) (hQP : Q ≤ P) :
    0 ≤ quarticMargin v b V W P Q := by
  have hu : 0 ≤ Q / P := div_nonneg hQ hP.le
  have hu1 : Q / P ≤ 1 := (div_le_one hP).2 hQP
  have hnorm := normalized_margin_nonneg hu hu1 hv hb hW hsum
  have hid : quarticMargin v b V W P Q =
      P ^ 4 * quarticMargin v b V W 1 (Q / P) := by
    unfold quarticMargin projectionBound
    field_simp [ne_of_gt hP]
  rw [hid]
  exact mul_nonneg (by positivity) hnorm

/-- The complete homogeneous inequality (20), including both orderings of
the two gradient norms and all allowable spectral defects. -/
theorem quartic_bound {v b V W P Q : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hsum : V + W ≤ 2 - v - b) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (27 / 128) * v * b * (P + Q) ^ 2 *
        (projectionBound v b V W * P ^ 2 + projectionBound b v W V * Q ^ 2) +
      (3 / 4) * v * b * (P + Q) *
        ((1 - 3 * (v - b) / 8) * P ^ 3 + (1 - 3 * (b - v) / 8) * Q ^ 3) ≤
      (67 / 50 + 27 * v * b / 100) * (P ^ 2 + Q ^ 2) * (b * P ^ 2 + v * Q ^ 2) := by
  suffices hm : 0 ≤ quarticMargin v b V W P Q by
    unfold quarticMargin at hm
    linarith
  by_cases hzero : P = 0 ∧ Q = 0
  · rcases hzero with ⟨rfl, rfl⟩
    simp [quarticMargin]
  rcases le_total Q P with hQP | hPQ
  · have hPpos : 0 < P := by
      by_contra h
      have : P = 0 := by linarith
      have : Q = 0 := by linarith
      exact hzero ⟨‹P = 0›, this⟩
    exact ordered_margin_nonneg hv hb hW hsum hPpos hQ hQP
  · have hQpos : 0 < Q := by
      by_contra h
      have : Q = 0 := by linarith
      have : P = 0 := by linarith
      exact hzero ⟨this, ‹Q = 0›⟩
    rw [← quarticMargin_swap]
    exact ordered_margin_nonneg hb hv hV (by linarith) hQpos hP hPQ

/-- The quartic estimate after the two nonradial energy defects have been
removed. Here `P² = 5 |p|² / 3` and `Q² = 5 |q|² / 3`; the factor `9/25`
converts back to the gradient energies in the combined integrand. -/
theorem zero_defect_quartic_bound {v b V W P Q : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hsum : V + W ≤ 2 - v - b) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (3 / 10) * (P + Q) *
        ((1 - 3 * (v - b) / 8) * P ^ 3 + (1 - 3 * (b - v) / 8) * Q ^ 3) +
      (27 / 320) * (P + Q) ^ 2 *
        (projectionBound v b V W * P ^ 2 + projectionBound b v W V * Q ^ 2) -
      (2 / 5) * (17 / 10) * (P ^ 2 + Q ^ 2) * (P ^ 2 / v + Q ^ 2 / b) ≤
      -(2 / 5 - 3 * v * b / 10) * (9 / 25) *
        (P ^ 2 + Q ^ 2) * (P ^ 2 / v + Q ^ 2 / b) := by
  have hm : 0 ≤ quarticMargin v b V W P Q := by
    unfold quarticMargin
    exact sub_nonneg.mpr (quartic_bound hv hb hV hW hsum hP hQ)
  have hmul := mul_nonneg (show 0 ≤ 2 / (5 * v * b) by positivity) hm
  have hid : 2 / (5 * v * b) * quarticMargin v b V W P Q =
      -(2 / 5 - 3 * v * b / 10) * (9 / 25) *
        (P ^ 2 + Q ^ 2) * (P ^ 2 / v + Q ^ 2 / b) -
      ((3 / 10) * (P + Q) *
        ((1 - 3 * (v - b) / 8) * P ^ 3 + (1 - 3 * (b - v) / 8) * Q ^ 3) +
      (27 / 320) * (P + Q) ^ 2 *
        (projectionBound v b V W * P ^ 2 + projectionBound b v W V * Q ^ 2) -
      (2 / 5) * (17 / 10) * (P ^ 2 + Q ^ 2) * (P ^ 2 / v + Q ^ 2 / b)) := by
    unfold quarticMargin
    field_simp
    ring
  rw [hid] at hmul
  linarith

end

end PositiveEinsteinFour.Quartic

end OAI
