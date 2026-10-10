import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HorizontalCompactification
import Mathlib.Topology.Compactness.Compact

namespace OAI

/-! # Joint continuity of the compactified finite recurrence -/

open Filter Topology

namespace DefocusingNLS

/-- Real spectral part, shift, coupling, and the two normalized initial coordinates. -/
abbrev HorizontalParameters := ℝ × ℝ × ℝ × ℂ × ℂ

noncomputable def horizontalStateAt (ell : ℕ) (h : ℝ) (n : ℕ)
    (x : ℝ × HorizontalParameters) : ℂ × ℂ :=
  horizontalState ell h x.2.1 x.2.2.1 x.2.2.2.1 x.1 x.2.2.2.2.1 x.2.2.2.2.2 n

noncomputable def horizontalDifferenceAt (ell n : ℕ) (h : ℝ)
    (x : ℝ × HorizontalParameters) : ℂ :=
  horizontalDifference ell n h x.2.1 x.2.2.1 x.2.2.2.1 x.1
    (horizontalStateAt ell h n x).1 (horizontalStateAt ell h n x).2

theorem continuousAt_horizontalStateAt (ell : ℕ) (h : ℝ) (n : ℕ)
    (p : HorizontalParameters) : ContinuousAt (horizontalStateAt ell h n) (0, p) := by
  induction n with
  | zero =>
    change ContinuousAt (fun x : ℝ × HorizontalParameters =>
      (x.2.2.2.2.1, x.2.2.2.2.2)) (0, p)
    fun_prop
  | succ n ih =>
    have hd : ContinuousAt (horizontalDifferenceAt ell n h) (0, p) := by
      unfold horizontalDifferenceAt horizontalDifference
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · simp
    change ContinuousAt (fun x : ℝ × HorizontalParameters =>
      ((horizontalStateAt ell h n x).1 - horizontalDifferenceAt ell n h x,
        (horizontalStateAt ell h n x).2 - (x.1 : ℂ) *
          ((horizontalStateAt ell h n x).1 - horizontalDifferenceAt ell n h x))) (0, p)
    fun_prop

theorem continuousAt_horizontalDifferenceAt (ell n : ℕ) (h : ℝ)
    (p : HorizontalParameters) : ContinuousAt (horizontalDifferenceAt ell n h) (0, p) := by
  have hc := continuousAt_horizontalStateAt ell h n p
  unfold horizontalDifferenceAt horizontalDifference
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · simp

noncomputable def horizontalFormAt (ell : ℕ) (x : ℝ × HorizontalParameters) : ℝ :=
  ((ell : ℝ) + 5) * Complex.normSq x.2.2.2.2.1 +
    horizontalIncrementSum ell 1 x.2.1 x.2.2.1 x.2.2.2.1 x.1 x.2.2.2.2.1 x.2.2.2.2.2 8 +
    horizontalIncrementSum ell (-1) x.2.1 x.2.2.1 x.2.2.2.1 x.1 x.2.2.2.2.1 x.2.2.2.2.2 8

theorem continuousAt_horizontalFormAt (ell : ℕ) (p : HorizontalParameters) :
    ContinuousAt (horizontalFormAt ell) (0, p) := by
  have hsum (h : ℝ) : ContinuousAt (fun x : ℝ × HorizontalParameters =>
      horizontalIncrementSum ell h x.2.1 x.2.2.1 x.2.2.2.1 x.1 x.2.2.2.2.1 x.2.2.2.2.2 8)
      (0, p) := by
    unfold horizontalIncrementSum
    apply tendsto_finsetSum
    intro n hn
    change ContinuousAt (fun x : ℝ × HorizontalParameters =>
      (x.2.1 + n - 5 / 2) * Complex.normSq (horizontalDifferenceAt ell n h x)) (0, p)
    have hc := continuousAt_horizontalDifferenceAt ell n h p
    fun_prop
  unfold horizontalFormAt
  fun_prop

/-- Compactness makes the positive limiting form uniform over all normalized
initial data and spectral parameters in a compact set. -/
theorem eventually_horizontalForm_positive (ell : ℕ) (P : Set HorizontalParameters)
    (hP : IsCompact P) (hσ : ∀ p ∈ P, -(1 / 32 : ℝ) ≤ p.1)
    (hZ : ∀ p ∈ P, p.2.2.1 ≠ 0)
    (hBC : ∀ p ∈ P, p.2.2.2.1 ≠ 0 ∨ p.2.2.2.2 ≠ 0) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ p ∈ P, 0 < horizontalFormAt ell (τ, p) := by
  apply hP.eventually_forall_of_forall_eventually
  intro p hp
  have hz : 0 < horizontalFormAt ell (0, p) :=
    horizontal_limiting_form_pos ell p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
      (hσ p hp) (hZ p hp) (hBC p hp)
  exact (continuousAt_horizontalFormAt ell p).eventually (eventually_gt_nhds hz)

end DefocusingNLS

end OAI
