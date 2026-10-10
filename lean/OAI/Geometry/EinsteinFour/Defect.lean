import Mathlib.Tactic

namespace OAI

/-! Exact scalar certificates controlling the energy defects in equation (19). -/

namespace PositiveEinsteinFour.Defect

noncomputable section

def A0 (v : ℝ) : ℝ := (27 / 320) * v * (15 / 2 + 2 * v / 3)
def L0 (v : ℝ) : ℝ := (9 / 20) * v * (7 / 4 - 3 * v / 4)
def C0 (v : ℝ) : ℝ := (7 / 5) * (17 / 10) - A0 v - L0 v
def discriminantNumerator (v : ℝ) : ℝ :=
  4 * C0 v * (((17 / 10) - A0 v) * (2 - v) + (2 / 5) * (17 / 10) * v) -
    (2 - v) * (2 * A0 v + L0 v) ^ 2

private theorem C0_0 {v : ℝ} (hlo : 0 ≤ v) (hhi : v ≤ 1) :
    1 / 2 ≤ C0 v := by
  have hz : 0 ≤ v - 0 := by linarith
  have hw : 0 ≤ 1 - v := by linarith
  have hcert : 3200 * (C0 v - 1 / 2) =
      6016 * (1 - v) ^ 2 +
      7487 * (v - 0) * (1 - v) +
      2371 * (v - 0) ^ 2 := by
    unfold C0 A0 L0
    ring
  have hp : 0 ≤ 3200 * (C0 v - 1 / 2) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem C0_1 {v : ℝ} (hlo : 1 ≤ v) (hhi : v ≤ 2) :
    1 / 2 ≤ C0 v := by
  have hz : 0 ≤ v - 1 := by linarith
  have hw : 0 ≤ 2 - v := by linarith
  have hcert : 3200 * (C0 v - 1 / 2) =
      2371 * (2 - v) ^ 2 +
      1997 * (v - 1) * (2 - v) +
      526 * (v - 1) ^ 2 := by
    unfold C0 A0 L0
    ring
  have hp : 0 ≤ 3200 * (C0 v - 1 / 2) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem disc_0 {v : ℝ} (hlo : 0 ≤ v) (hhi : v ≤ 1) :
    1 / 2 ≤ discriminantNumerator v := by
  have hz : 0 ≤ v - 0 := by linarith
  have hw : 0 ≤ 1 - v := by linarith
  have hcert : 160000 * (discriminantNumerator v - 1 / 2) =
      5098880 * (1 - v) ^ 5 +
      18922336 * (v - 0) * (1 - v) ^ 4 +
      26833814 * (v - 0) ^ 2 * (1 - v) ^ 3 +
      18127631 * (v - 0) ^ 3 * (1 - v) ^ 2 +
      5827264 * (v - 0) ^ 4 * (1 - v) +
      728216 * (v - 0) ^ 5 := by
    unfold discriminantNumerator C0 A0 L0
    ring
  have hp : 0 ≤ 160000 * (discriminantNumerator v - 1 / 2) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem disc_1 {v : ℝ} (hlo : 1 ≤ v) (hhi : v ≤ 2) :
    1 / 2 ≤ discriminantNumerator v := by
  have hz : 0 ≤ v - 1 := by linarith
  have hw : 0 ≤ 2 - v := by linarith
  have hcert : 160000 * (discriminantNumerator v - 1 / 2) =
      728216 * (2 - v) ^ 5 +
      1454896 * (v - 1) * (2 - v) ^ 4 +
      638159 * (v - 1) ^ 2 * (2 - v) ^ 3 +
      334916 * (v - 1) ^ 3 * (2 - v) ^ 2 +
      903484 * (v - 1) ^ 4 * (2 - v) +
      498272 * (v - 1) ^ 5 := by
    unfold discriminantNumerator C0 A0 L0
    ring
  have hp : 0 ≤ 160000 * (discriminantNumerator v - 1 / 2) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

theorem C0_pos {v : ℝ} (hv : 0 ≤ v) (hv2 : v ≤ 2) : 0 < C0 v := by
  by_cases hv1 : v ≤ 1
  · linarith [C0_0 hv hv1]
  · linarith [C0_1 (le_of_lt (lt_of_not_ge hv1)) hv2]

theorem disc_pos {v : ℝ} (hv : 0 ≤ v) (hv2 : v ≤ 2) : 0 < discriminantNumerator v := by
  by_cases hv1 : v ≤ 1
  · linarith [disc_0 hv hv1]
  · linarith [disc_1 (le_of_lt (lt_of_not_ge hv1)) hv2]

private theorem negative_quadratic {C B D : ℝ} (hC : 0 < C)
    (hdisc : B ^ 2 < 4 * C * D) (u : ℝ) : -C + B * u - D * u ^ 2 < 0 := by
  have hD : 0 < D := by nlinarith [sq_nonneg B]
  have hid : 4 * D * (C - B * u + D * u ^ 2) =
      (2 * D * u - B) ^ 2 + (4 * C * D - B ^ 2) := by ring
  have hpos : 0 < 4 * D * (C - B * u + D * u ^ 2) := by
    rw [hid]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sub_pos.mpr hdisc)
  have hpoly : 0 < C - B * u + D * u ^ 2 :=
    (mul_pos_iff_of_pos_left (by positivity : 0 < 4 * D)).mp hpos
  linarith

/-- The exact upper bound for the derivative with respect to an energy defect
is negative on the open spectral interval, for every real energy ratio. -/
theorem energy_defect_derivative_neg {v : ℝ} (hv : 0 < v) (hv2 : v < 2) (u : ℝ) :
    A0 v * (1 + u) ^ 2 + L0 v * (1 + u) -
      (17 / 10) * (7 / 5 + (1 + 2 * v / (5 * (2 - v))) * u ^ 2) < 0 := by
  let D : ℝ := (17 / 10) - A0 v + 2 * (17 / 10) * v / (5 * (2 - v))
  have hden : 0 < 2 - v := by linarith
  have hid : discriminantNumerator v =
      (2 - v) * (4 * C0 v * D - (2 * A0 v + L0 v) ^ 2) := by
    unfold discriminantNumerator D
    field_simp [ne_of_gt hden]
  have hdisc : (2 * A0 v + L0 v) ^ 2 < 4 * C0 v * D := by
    have hp := disc_pos hv.le hv2.le
    rw [hid] at hp
    have := (mul_pos_iff_of_pos_left hden).mp hp
    linarith
  have hquad := negative_quadratic (C0_pos hv.le hv2.le) hdisc u
  have heq : A0 v * (1 + u) ^ 2 + L0 v * (1 + u) -
      (17 / 10) * (7 / 5 + (1 + 2 * v / (5 * (2 - v))) * u ^ 2) =
      -C0 v + (2 * A0 v + L0 v) * u - D * u ^ 2 := by
    unfold C0 D
    ring
  rwa [heq]

end

end PositiveEinsteinFour.Defect

end OAI
