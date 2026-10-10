import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic

namespace OAI

/-!
# Smooth periodic staircases

An explicit degree-one smooth staircase with spacing `h` and transition
half-width `δ`. The transition in the cell `[nh,(n+1)h]` is centered at
`(n+1/2)h`. The floor jumps cancel because the transition is flat near
the cell endpoints.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- A smooth staircase with transitions near the half-shifted `h` lattice. -/
def smoothStaircase (h δ x : ℝ) : ℝ :=
  h * ((⌊x / h⌋ : ℝ) + Real.smoothTransition
    ((x - h * (⌊x / h⌋ : ℝ) - (h / 2 - δ)) / (2 * δ)))

private theorem cell_lower {h : ℝ} (hh : 0 < h) (x : ℝ) :
    h * (⌊x / h⌋ : ℝ) ≤ x := by
  have hx := (le_div_iff₀ hh).mp (Int.floor_le (x / h))
  simpa only [mul_comm] using hx

private theorem cell_upper {h : ℝ} (hh : 0 < h) (x : ℝ) :
    x < h * ((⌊x / h⌋ : ℝ) + 1) := by
  have hx := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (x / h))
  simpa only [mul_comm] using hx

theorem smoothStaircase_lower {h : ℝ} (hh : 0 ≤ h) (δ x : ℝ) :
    h * (⌊x / h⌋ : ℝ) ≤ smoothStaircase h δ x := by
  unfold smoothStaircase
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right
    (Real.smoothTransition.nonneg _)) hh

theorem smoothStaircase_upper {h : ℝ} (hh : 0 ≤ h) (δ x : ℝ) :
    smoothStaircase h δ x ≤ h * ((⌊x / h⌋ : ℝ) + 1) := by
  unfold smoothStaircase
  exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _)
    (Real.smoothTransition.le_one _)) hh

/-- The staircase is a degree-one lift with period increment `h`. -/
theorem smoothStaircase_add_period {h : ℝ} (hh : 0 < h) (δ x : ℝ) :
    smoothStaircase h δ (x + h) = smoothStaircase h δ x + h := by
  have hfloor : ⌊(x + h) / h⌋ = ⌊x / h⌋ + 1 := by
    rw [add_div, div_self hh.ne', Int.floor_add_one]
  have hresid : x + h - h * ((⌊x / h⌋ : ℝ) + 1) = x - h * (⌊x / h⌋ : ℝ) := by
    ring
  simp only [smoothStaircase, hfloor, Int.cast_add, Int.cast_one, hresid]
  ring

/-- Uniform displacement is bounded by one grid spacing. -/
theorem abs_smoothStaircase_sub_le {h : ℝ} (hh : 0 < h) (δ x : ℝ) :
    |smoothStaircase h δ x - x| ≤ h := by
  have hl := smoothStaircase_lower hh.le δ x
  have hu := smoothStaircase_upper hh.le δ x
  have hcl := cell_lower hh x
  have hcu := cell_upper hh x
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Positive transition width gives a monotone staircase. -/
theorem monotone_smoothStaircase {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) :
    Monotone (smoothStaircase h δ) := by
  intro x y hxy
  have hfloor := Int.floor_mono ((div_le_div_iff_of_pos_right hh).mpr hxy)
  rcases lt_or_eq_of_le hfloor with hlt | heq
  · have hi : ⌊x / h⌋ + 1 ≤ ⌊y / h⌋ := Int.add_one_le_iff.mpr hlt
    have hir : (⌊x / h⌋ : ℝ) + 1 ≤ (⌊y / h⌋ : ℝ) := by exact_mod_cast hi
    exact (smoothStaircase_upper hh.le δ x).trans
      ((mul_le_mul_of_nonneg_left hir hh.le).trans (smoothStaircase_lower hh.le δ y))
  · simp only [smoothStaircase, heq]
    apply mul_le_mul_of_nonneg_left _ hh.le
    apply add_le_add (le_refl _)
    apply Real.smoothTransition.monotone
    apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * δ)).mpr
    linarith

/-- Around a cell boundary the floor jump cancels the completed transition,
so the staircase is identically the lattice value. -/
private theorem smoothStaircase_eq_near_lattice {h δ x : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (n : ℤ)
    (hl : h * n - h / 4 < x) (hu : x < h * n + h / 4) :
    smoothStaircase h δ x = h * n := by
  have hlow : n - 1 ≤ ⌊x / h⌋ := by
    apply Int.le_floor.mpr
    apply (le_div_iff₀ hh).mpr
    simp only [Int.cast_sub, Int.cast_one]
    nlinarith
  have hupp : ⌊x / h⌋ ≤ n := by
    apply Int.floor_le_iff.mpr
    apply (div_lt_iff₀ hh).mpr
    nlinarith
  have hcases : ⌊x / h⌋ = n - 1 ∨ ⌊x / h⌋ = n := by omega
  rcases hcases with hleft | hright
  · have harg : 1 ≤ (x - h * ((n - 1 : ℤ) : ℝ) - (h / 2 - δ)) / (2 * δ) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * δ)).mpr
      simp only [Int.cast_sub, Int.cast_one]
      nlinarith
    simp only [smoothStaircase, hleft]
    rw [Real.smoothTransition.one_of_one_le harg]
    push_cast
    ring
  · have harg : (x - h * (n : ℝ) - (h / 2 - δ)) / (2 * δ) ≤ 0 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * δ)).mpr
      nlinarith
    simp only [smoothStaircase, hright, Real.smoothTransition.zero_of_nonpos harg, add_zero]

private theorem smoothStaircase_eventually_eq_lattice {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (n : ℤ) :
    smoothStaircase h δ =ᶠ[𝓝 (h * n)] (fun _ => h * n) := by
  filter_upwards [Ioo_mem_nhds (by linarith : h * (n : ℝ) - h / 4 < h * n)
    (by linarith : h * (n : ℝ) < h * n + h / 4)] with y hy
  exact smoothStaircase_eq_near_lattice hh hδ hδh n hy.1 hy.2

private theorem smoothStaircase_eventually_eq_cell {h δ x : ℝ}
    (hh : 0 < h) (n : ℤ) (hl : h * n < x) (hu : x < h * (n + 1)) :
    smoothStaircase h δ =ᶠ[𝓝 x] (fun y => h * ((n : ℝ) +
      Real.smoothTransition ((y - h * n - (h / 2 - δ)) / (2 * δ)))) := by
  filter_upwards [Ioo_mem_nhds hl hu] with y hy
  have hfloor : ⌊y / h⌋ = n := by
    apply Int.floor_eq_iff.mpr
    constructor
    · apply (le_div_iff₀ hh).mpr
      nlinarith [hy.1]
    · apply (div_lt_iff₀ hh).mpr
      nlinarith [hy.2]
  simp only [smoothStaircase, hfloor]

/-- The apparent jumps of the floor formula cancel; the staircase is smooth
at lattice points as well as inside every cell. -/
theorem contDiff_smoothStaircase {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) :
    ContDiff ℝ ∞ (smoothStaircase h δ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  let n : ℤ := ⌊x / h⌋
  by_cases hx : x = h * n
  · have heq : smoothStaircase h δ =ᶠ[𝓝 x] (fun _ => h * n) := by
      simpa only [hx] using smoothStaircase_eventually_eq_lattice hh hδ hδh n
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have hl : h * n < x := lt_of_le_of_ne (cell_lower hh x) (Ne.symm hx)
    have hu : x < h * (n + 1) := cell_upper hh x
    have hc : ContDiff ℝ ∞ (fun y : ℝ => h * ((n : ℝ) +
        Real.smoothTransition ((y - h * n - (h / 2 - δ)) / (2 * δ)))) := by
      fun_prop
    exact hc.contDiffAt.congr_of_eventuallyEq (smoothStaircase_eventually_eq_cell hh n hl hu)

private theorem transition_hasDerivAt_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    HasDerivAt Real.smoothTransition 0 t := by
  have hd : HasDerivWithinAt Real.smoothTransition 0 (Iic t) t :=
    (hasDerivWithinAt_const t (Iic t) (0 : ℝ)).congr
      (fun y hy => Real.smoothTransition.zero_of_nonpos (hy.trans ht))
      (Real.smoothTransition.zero_of_nonpos ht)
  have hzero := hd.deriv_eq_zero (uniqueDiffWithinAt_Iic t)
  simpa only [hzero] using
    ((Real.smoothTransition.contDiff (n := 1)).differentiable_one t).hasDerivAt

private theorem transition_hasDerivAt_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt Real.smoothTransition 0 t := by
  have hd : HasDerivWithinAt Real.smoothTransition 0 (Ici t) t :=
    (hasDerivWithinAt_const t (Ici t) (1 : ℝ)).congr
      (fun y hy => Real.smoothTransition.one_of_one_le (ht.trans hy))
      (Real.smoothTransition.one_of_one_le ht)
  have hzero := hd.deriv_eq_zero (uniqueDiffWithinAt_Ici t)
  simpa only [hzero] using
    ((Real.smoothTransition.contDiff (n := 1)).differentiable_one t).hasDerivAt

/-- The derivative of the monotone lift is everywhere nonnegative. -/
theorem deriv_smoothStaircase_nonneg {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (x : ℝ) :
    0 ≤ deriv (smoothStaircase h δ) x :=
  (monotone_smoothStaircase hh hδ).deriv_nonneg

/-- The derivative is supported in the open `δ`-bands about the half-shifted
lattice. The assertion includes the endpoints of each band. -/
theorem deriv_smoothStaircase_eq_zero {h δ x : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hfar : ∀ n : ℤ, δ ≤ |x - h * ((n : ℝ) + 1 / 2)|) :
    deriv (smoothStaircase h δ) x = 0 := by
  let n : ℤ := ⌊x / h⌋
  by_cases hx : x = h * n
  · have heq : smoothStaircase h δ =ᶠ[𝓝 x] (fun _ => h * n) := by
      simpa only [hx] using smoothStaircase_eventually_eq_lattice hh hδ hδh n
    exact ((hasDerivAt_const x (h * (n : ℝ))).congr_of_eventuallyEq heq).deriv
  · have hl : h * n < x := lt_of_le_of_ne (cell_lower hh x) (Ne.symm hx)
    have hu : x < h * (n + 1) := cell_upper hh x
    have htrans : HasDerivAt Real.smoothTransition 0
        ((x - h * n - (h / 2 - δ)) / (2 * δ)) := by
      rcases le_abs.mp (hfar n) with hr | hl
      · apply transition_hasDerivAt_zero_of_one_le
        apply (le_div_iff₀ (by positivity : 0 < 2 * δ)).mpr
        nlinarith
      · apply transition_hasDerivAt_zero_of_nonpos
        apply (div_le_iff₀ (by positivity : 0 < 2 * δ)).mpr
        nlinarith
    have harg : HasDerivAt
        (fun y : ℝ => (y - h * n - (h / 2 - δ)) / (2 * δ)) (1 / (2 * δ)) x :=
      (((hasDerivAt_id x).sub_const (h * n)).sub_const (h / 2 - δ)).div_const (2 * δ)
    have hcell : HasDerivAt (fun y : ℝ => h * ((n : ℝ) +
        Real.smoothTransition ((y - h * n - (h / 2 - δ)) / (2 * δ)))) 0 x := by
      convert! ((htrans.comp x harg).const_add (n : ℝ)).const_mul h using 1
      simp
    exact (hcell.congr_of_eventuallyEq (smoothStaircase_eventually_eq_cell hh n hl hu)).deriv

end CircleDomainRigidity.FiniteTransfer

end

end OAI
