import OAI.Analysis.CircleDomains.Selection.Staircase
import OAI.Analysis.CircleDomains.Selection.StaircaseMean

namespace OAI

/-!
# The randomly shifted smooth staircase family

Translating the explicit staircase places its transition bands at
`θ + hℤ`. The resulting family has the exact derivative mean required
for uniform random shifts, and retains the displacement and period
properties needed for periodic coordinate branches.
-/

open MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- The smooth staircase whose transition centers form `θ + hℤ`. -/
def shiftedStaircase (h δ θ x : ℝ) : ℝ :=
  smoothStaircase h δ ((x + h / 2) - θ) + θ - h / 2

theorem contDiff_shiftedStaircase {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (θ : ℝ) :
    ContDiff ℝ ∞ (shiftedStaircase h δ θ) := by
  have hP := contDiff_smoothStaircase hh hδ hδh
  unfold shiftedStaircase
  exact ((hP.comp ((contDiff_id.add contDiff_const).sub contDiff_const)).add
    contDiff_const).sub contDiff_const

theorem monotone_shiftedStaircase {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (θ : ℝ) :
    Monotone (shiftedStaircase h δ θ) := by
  intro x y hxy
  unfold shiftedStaircase
  exact sub_le_sub_right (add_le_add
    (monotone_smoothStaircase hh hδ (by linarith)) (le_refl θ)) (h / 2)

theorem abs_shiftedStaircase_sub_le {h : ℝ} (hh : 0 < h) (δ θ x : ℝ) :
    |shiftedStaircase h δ θ x - x| ≤ h := by
  have heq : shiftedStaircase h δ θ x - x =
      smoothStaircase h δ ((x + h / 2) - θ) - ((x + h / 2) - θ) := by
    unfold shiftedStaircase
    ring
  rw [heq]
  exact abs_smoothStaircase_sub_le hh δ _

theorem shiftedStaircase_add_period {h : ℝ} (hh : 0 < h) (δ θ x : ℝ) :
    shiftedStaircase h δ θ (x + h) = shiftedStaircase h δ θ x + h := by
  have heq : (x + h + h / 2) - θ = ((x + h / 2) - θ) + h := by ring
  simp only [shiftedStaircase, heq, smoothStaircase_add_period hh]
  ring

theorem shiftedStaircase_add_nat_mul_period {h : ℝ} (hh : 0 < h)
    (δ θ x : ℝ) (N : ℕ) :
    shiftedStaircase h δ θ (x + N * h) = shiftedStaircase h δ θ x + N * h := by
  induction N with
  | zero => simp
  | succ N ih =>
    have heq : x + (↑(N + 1) : ℝ) * h = (x + N * h) + h := by push_cast; ring
    rw [heq, shiftedStaircase_add_period hh, ih]
    push_cast
    ring

/-- Choosing reciprocal-integer spacing preserves additive period one. -/
theorem shiftedStaircase_add_one {N : ℕ} (hN : 0 < N) (δ θ x : ℝ) :
    shiftedStaircase (1 / (N : ℝ)) δ θ (x + 1) =
      shiftedStaircase (1 / (N : ℝ)) δ θ x + 1 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmul : (N : ℝ) * (1 / (N : ℝ)) = 1 := by field_simp [ne_of_gt hNr]
  simpa only [hmul] using shiftedStaircase_add_nat_mul_period
    (div_pos zero_lt_one hNr) δ θ x N

/-- Translation does not change the derivative multiplier. -/
theorem deriv_shiftedStaircase {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (θ x : ℝ) :
    deriv (shiftedStaircase h δ θ) x =
      deriv (smoothStaircase h δ) ((x + h / 2) - θ) := by
  have hP := (contDiff_smoothStaircase hh hδ hδh).differentiable (by simp)
  have harg : HasDerivAt (fun t : ℝ => (t + h / 2) - θ) 1 x :=
    ((hasDerivAt_id x).add_const (h / 2)).sub_const θ
  have hd := (((hP ((x + h / 2) - θ)).hasDerivAt.comp x harg).add_const θ).sub_const (h / 2)
  convert! hd.deriv using 1
  simp

theorem deriv_shiftedStaircase_nonneg {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (θ x : ℝ) :
    0 ≤ deriv (shiftedStaircase h δ θ) x :=
  (monotone_shiftedStaircase hh hδ θ).deriv_nonneg

/-- Only the open `δ`-neighborhoods of the shifted lattice can support
nonzero derivative, with zero derivative also at their endpoints. -/
theorem deriv_shiftedStaircase_eq_zero {h δ θ x : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hfar : ∀ n : ℤ, δ ≤ |x - (θ + h * n)|) :
    deriv (shiftedStaircase h δ θ) x = 0 := by
  rw [deriv_shiftedStaircase hh hδ hδh]
  apply deriv_smoothStaircase_eq_zero hh hδ hδh
  intro n
  convert hfar n using 1
  congr 1
  ring

theorem continuous_shiftedStaircase_deriv {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (x : ℝ) :
    Continuous (fun θ => deriv (shiftedStaircase h δ θ) x) := by
  simp_rw [deriv_shiftedStaircase hh hδ hδh]
  have hP : ContDiff ℝ 1 (smoothStaircase h δ) :=
    (contDiff_smoothStaircase hh hδ hδh).of_le (by simp)
  exact hP.continuous_deriv_one.comp (continuous_const.sub continuous_id)

/-- Actual uniform shifts of the constructed staircase have derivative
integral exactly `h`. -/
theorem integral_shiftedStaircase_deriv {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (x : ℝ) :
    (∫ θ in (0 : ℝ)..h, deriv (shiftedStaircase h δ θ) x) = h := by
  simp_rw [deriv_shiftedStaircase hh hδ hδh]
  exact integral_shifted_deriv_eq_period
    ((contDiff_smoothStaircase hh hδ hδh).of_le (by simp))
    (smoothStaircase_add_period hh δ) (x + h / 2)

theorem average_shiftedStaircase_deriv {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (x : ℝ) :
    (∫ θ in (0 : ℝ)..h, deriv (shiftedStaircase h δ θ) x) / h = 1 := by
  rw [integral_shiftedStaircase_deriv hh hδ hδh, div_self hh.ne']

/-- A cutoff between the original coordinate and the actual shifted
staircase preserves mean multiplier one. -/
theorem integral_shiftedStaircase_cutoff_multiplier {h δ : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (x χ : ℝ) :
    (∫ θ in (0 : ℝ)..h, (1 - χ) + χ * deriv (shiftedStaircase h δ θ) x) = h := by
  simp_rw [deriv_shiftedStaircase hh hδ hδh]
  exact integral_cutoff_multiplier
    ((contDiff_smoothStaircase hh hδ hδh).of_le (by simp))
    (smoothStaircase_add_period hh δ) (x + h / 2) χ

end CircleDomainRigidity.FiniteTransfer

end

end OAI
