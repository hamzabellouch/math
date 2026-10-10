import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactRationalGlobal
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombTargetLipschitz
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibrationGraphBudget

namespace OAI

/-! Scaled rational contact coordinates retain the actual Coulomb
calibration, with the coordinate and scalar-evaluation errors added
explicitly. The gap follows from the proved separated-density estimate. -/

noncomputable section
namespace ContinuumCoulomb.ContactCalibratedGeometry
open ContactMediator MediatorIteration
open scoped BigOperators

def position (d : SquareLatticeHeisenberg) (P : ℕ) (q : ℚ)
    (ℓ : GlobalEdge d → ℚ) (x : GlobalSite d) : ℚ × ℚ :=
  (q * (ContactRationalGlobal.position d P ℓ x).1,
    q * (ContactRationalGlobal.position d P ℓ x).2)

def point (d : SquareLatticeHeisenberg) (P : ℕ) (q : ℚ)
    (ℓ : GlobalEdge d → ℚ) (x : GlobalSite d) : ContactPoint :=
  (q : ℝ) • ContactRationalGlobal.point d P ℓ x

theorem position_cast (d : SquareLatticeHeisenberg) (P : ℕ) (q : ℚ)
    (ℓ : GlobalEdge d → ℚ) (x : GlobalSite d) :
    contactPoint (position d P q ℓ x).1 (position d P q ℓ x).2 = point d P q ℓ x := by
  unfold position point
  rw [← ContactRationalGlobal.position_cast]
  ext i
  fin_cases i <;> simp [contactPoint, Rat.cast_mul]

theorem distance (d : SquareLatticeHeisenberg) (P : ℕ) {q : ℚ} (hq : 0 < q)
    (ℓ : GlobalEdge d → ℚ) (x y : GlobalSite d) :
    dist (point d P q ℓ x) (point d P q ℓ y) =
      (q : ℝ) * dist (ContactRationalGlobal.point d P ℓ x)
        (ContactRationalGlobal.point d P ℓ y) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [point, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hqr]

theorem edge_error (d : SquareLatticeHeisenberg) (W G P : ℕ) {q : ℚ} (hq : 0 < q)
    (ℓ : GlobalEdge d → ℚ)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (a : GlobalEdge d) :
    |dist (point d P q ℓ ((finalGraph d.bonds W G).left a))
      (point d P q ℓ ((finalGraph d.bonds W G).right a)) - (q : ℝ) * ℓ a| ≤
        (q : ℝ) * (72 * ((P : ℝ) + 1)⁻¹) := by
  rw [distance d P hq, ← mul_sub, abs_mul, abs_of_pos (show (0 : ℝ) < q by exact_mod_cast hq)]
  exact mul_le_mul_of_nonneg_left (ContactRationalGlobal.edge_error d W G P ℓ hℓ a)
    (by exact_mod_cast hq.le)

theorem separation (d : SquareLatticeHeisenberg) (W G P : ℕ) {q : ℚ} (hq : 0 < q)
    (ℓ : GlobalEdge d → ℚ) (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (x y : GlobalSite d) (hne : x ≠ y) :
    (9 / 10 : ℝ) * q ≤ dist (point d P q ℓ x) (point d P q ℓ y) := by
  rw [distance d P hq]
  have h := mul_le_mul_of_nonneg_left
    (ContactRationalGlobal.separation d W G P ℓ hP hℓ x y hne)
    (show (0 : ℝ) ≤ q by exact_mod_cast hq.le)
  simpa only [mul_comm] using h

theorem nonedge_separation (d : SquareLatticeHeisenberg) (W G P : ℕ) {q : ℚ}
    (hq : 0 < q) (ℓ : GlobalEdge d → ℚ) (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (x y : GlobalSite d) (hne : x ≠ y) (hn : Nonedge d W G x y) :
    (6 / 5 : ℝ) * q < dist (point d P q ℓ x) (point d P q ℓ y) := by
  rw [distance d P hq]
  have h := mul_lt_mul_of_pos_left
    (ContactRationalGlobal.nonedge_separation d W G P ℓ hP hℓ x y hne hn)
    (show (0 : ℝ) < q by exact_mod_cast hq)
  simpa only [mul_comm] using h

theorem coordinate_bound (d : SquareLatticeHeisenberg) (P : ℕ) {q : ℚ} (hq : 0 < q)
    (ℓ : GlobalEdge d → ℚ) (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    {M : ℝ} (hcoord : ∀ j k, |(contactGridAxis (d.coordinate j) k : ℝ)| ≤ M)
    (x : GlobalSite d) (i : Fin 2) : |point d P q ℓ x i| ≤ (q : ℝ) * (17 * M + 17) := by
  change |(q : ℝ) * ContactRationalGlobal.point d P ℓ x i| ≤ _
  rw [abs_mul, abs_of_pos (show (0 : ℝ) < q by exact_mod_cast hq)]
  exact mul_le_mul_of_nonneg_left
    (ContactRationalGlobal.coordinate_bound d P ℓ hP hℓ hcoord x i)
    (by exact_mod_cast hq.le)

theorem calibrated_edge_residual (d : SquareLatticeHeisenberg) (W G P : ℕ)
    {q : ℚ} (hq : 0 < q) (ℓ : GlobalEdge d → ℚ) (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    {freq D scale τ ε : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    (hleak : 2 * localLeakageBound freq D ≤ localDualMass freq / 2)
    (hDq : D ≤ (9 / 10 : ℝ) * q) (hscale : 0 ≤ scale) (hτ : 0 ≤ τ)
    (K : GlobalEdge d → ℝ) (hK : ∀ a, 0 ≤ K a)
    (hres : ∀ a, |scale * planarHopping ((q : ℝ) * ℓ a) -
      coulombHoppingTarget freq τ (K a) ((q : ℝ) * ℓ a)| ≤ ε)
    (a : GlobalEdge d)
    (hne : (finalGraph d.bonds W G).left a ≠ (finalGraph d.bonds W G).right a) :
    let r := dist (point d P q ℓ ((finalGraph d.bonds W G).left a))
      (point d P q ℓ ((finalGraph d.bonds W G).right a))
    |scale * planarHopping r - coulombHoppingTarget freq τ (K a) r| ≤
      ε + (scale * (planarHoppingLipschitzConstant : ℝ) +
        coulombTargetLipschitzConstant freq τ (K a)) * ((q : ℝ) * (72 * ((P : ℝ) + 1)⁻¹)) := by
  intro r
  have hr : D ≤ r := hDq.trans (separation d W G P hq ℓ hP hℓ _ _ hne)
  have ht : D ≤ (q : ℝ) * ℓ a := by
    have hl := (hℓ a).1
    have htol : (9 / 10 : ℝ) ≤ ℓ a := by
      unfold contactLengthTolerance at hl
      linarith
    exact hDq.trans (by nlinarith [show (0 : ℝ) < q by exact_mod_cast hq])
  have hrgap := localizedCoulombProfile_gap hfreq hD hleak hr
  have htgap := localizedCoulombProfile_gap hfreq hD hleak ht
  have hdiff := calibratedResidual_abs_sub hfreq hτ (hK a) hscale r ((q : ℝ) * ℓ a)
    hrgap htgap
  have hc : 0 ≤ scale * (planarHoppingLipschitzConstant : ℝ) +
      coulombTargetLipschitzConstant freq τ (K a) :=
    add_nonneg (mul_nonneg hscale (by positivity))
      (coulombTargetLipschitzConstant_nonnegative freq (K a) hτ)
  have hd := mul_le_mul_of_nonneg_left (edge_error d W G P hq ℓ hℓ a) hc
  have htri := abs_add_le
    (scale * planarHopping r - coulombHoppingTarget freq τ (K a) r -
      (scale * planarHopping ((q : ℝ) * ℓ a) - coulombHoppingTarget freq τ (K a) ((q : ℝ) * ℓ a)))
    (scale * planarHopping ((q : ℝ) * ℓ a) - coulombHoppingTarget freq τ (K a) ((q : ℝ) * ℓ a))
  rw [sub_add_cancel] at htri
  linarith [hres a]

end ContinuumCoulomb.ContactCalibratedGeometry

end

end OAI
