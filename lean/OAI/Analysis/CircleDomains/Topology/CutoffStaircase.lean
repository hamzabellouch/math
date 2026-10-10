import OAI.Analysis.CircleDomains.Topology.ComponentControl

namespace OAI

/-!
# Joining a coordinate to a staircase outside a core

These are the differential and periodicity calculations for the actual
cutoff modification `u + χ (P ∘ u - u)` in finite transfer. They apply to
ordinary real branches and hence also to compatible periodic branches.
-/

open Filter

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def cutoffStaircase {X : Type*} (u χ : X → ℝ) (P : ℝ → ℝ) (x : X) : ℝ :=
  u x + χ x * (P (u x) - u x)

/-- The modified differential has the original gradient multiplier and
one error term supported on the cutoff transition. -/
theorem hasFDerivAt_cutoffStaircase {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u χ : E → ℝ} {P : ℝ → ℝ} {x : E} {du dχ : E →L[ℝ] ℝ} {p : ℝ}
    (hu : HasFDerivAt u du x) (hχ : HasFDerivAt χ dχ x) (hP : HasDerivAt P p (u x)) :
    HasFDerivAt (cutoffStaircase u χ P)
      ((1 - χ x + χ x * p) • du + (P (u x) - u x) • dχ) x := by
  have hd := hu.add (hχ.mul ((hP.comp_hasFDerivAt x hu).sub hu))
  convert hd using 1
  · rfl
  · ext v
    simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, Pi.sub_apply,
      Function.comp_apply]
    ring

/-- Smooth input coordinates, staircase and cutoff give a smooth modification. -/
theorem contDiff_cutoffStaircase {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞} {u χ : E → ℝ} {P : ℝ → ℝ}
    (hu : ContDiff ℝ n u) (hχ : ContDiff ℝ n χ) (hP : ContDiff ℝ n P) :
    ContDiff ℝ n (cutoffStaircase u χ P) :=
  hu.add (hχ.mul ((hP.comp hu).sub hu))

/-- The original coordinate is retained exactly where the cutoff is zero. -/
theorem cutoffStaircase_of_zero {X : Type*} {u χ : X → ℝ} {P : ℝ → ℝ} {x : X}
    (hχ : χ x = 0) : cutoffStaircase u χ P x = u x := by
  simp [cutoffStaircase, hχ]

/-- The staircase is used exactly where the cutoff is one. -/
theorem cutoffStaircase_of_one {X : Type*} {u χ : X → ℝ} {P : ℝ → ℝ} {x : X}
    (hχ : χ x = 1) : cutoffStaircase u χ P x = P (u x) := by
  simp [cutoffStaircase, hχ]

/-- A staircase with unit additive period preserves the coordinate's
additive deck-transformation law under an invariant cutoff. -/
theorem cutoffStaircase_period {X : Type*} {u χ : X → ℝ} {P : ℝ → ℝ}
    (T : X → X) (hu : ∀ x, u (T x) = u x + 1) (hχ : ∀ x, χ (T x) = χ x)
    (hP : ∀ t, P (t + 1) = P t + 1) (x : X) :
    cutoffStaircase u χ P (T x) = cutoffStaircase u χ P x + 1 := by
  simp only [cutoffStaircase, hu, hχ, hP]
  ring

/-- The cutoff does not enlarge the staircase's uniform displacement. -/
theorem abs_cutoffStaircase_sub_le {X : Type*} {u χ : X → ℝ} {P : ℝ → ℝ}
    {x : X} {h : ℝ} (hχ0 : 0 ≤ χ x) (hχ1 : χ x ≤ 1)
    (hP : |P (u x) - u x| ≤ h) :
    |cutoffStaircase u χ P x - u x| ≤ h := by
  have hχ : |χ x| ≤ 1 := abs_le.mpr ⟨by linarith, hχ1⟩
  calc
    |cutoffStaircase u χ P x - u x| = |χ x| * |P (u x) - u x| := by
      simp [cutoffStaircase, abs_mul]
    _ ≤ 1 * h := mul_le_mul hχ hP (abs_nonneg _) (by norm_num)
    _ = h := one_mul h

/-- The leading differential multiplier is nonnegative for a monotone
staircase and a cutoff taking values in `[0,1]`. -/
theorem cutoff_multiplier_nonneg {P : ℝ → ℝ} (hP : Monotone P)
    {χ x : ℝ} (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) :
    0 ≤ 1 - χ + χ * deriv P x :=
  add_nonneg (sub_nonneg.mpr hχ1) (mul_nonneg hχ0 hP.deriv_nonneg)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
