import OAI.Geometry.IsometricImmersion.Darboux.QPrincipal
import OAI.Geometry.IsometricImmersion.Calculus.StateJetSegment
import Mathlib.Analysis.Calculus.Deriv.AffineMap

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def qHeightJetSegment (z0 z : Coord → ℝ) (sigma : ℝ) (p : Coord) : DarbouxState :=
  stateSegment (qSolutionJet z0 p) (qSolutionJet z p) sigma

@[simp] theorem stateSegment_zero (w0 w1 : DarbouxState) : stateSegment w0 w1 0 = w0 := by
  simp [stateSegment]

@[simp] theorem stateSegment_one (w0 w1 : DarbouxState) : stateSegment w0 w1 1 = w1 := by
  simp [stateSegment]

theorem stateSegment_hasDerivAt (w0 w1 : DarbouxState) (sigma : ℝ) :
    HasDerivAt (stateSegment w0 w1) (w1 - w0) sigma := by
  have he : (AffineMap.lineMap w0 w1 : ℝ → DarbouxState) = stateSegment w0 w1 := by
    funext t
    ext i
    simp [AffineMap.lineMap_apply_module, stateSegment]
  rw [← he]
  exact AffineMap.hasDerivAt_lineMap

theorem stateSegment_continuous (w0 w1 : DarbouxState) : Continuous (stateSegment w0 w1) :=
  continuous_iff_continuousAt.mpr (fun sigma => (stateSegment_hasDerivAt w0 w1 sigma).continuousAt)

theorem statePoint_qHeightJetSegment (z0 z : Coord → ℝ) (sigma : ℝ) (p : Coord) :
    statePoint (qHeightJetSegment z0 z sigma p) = p := by
  rw [qHeightJetSegment, statePoint_segment (by simp only [statePoint_qSolutionJet]),
    statePoint_qSolutionJet]

theorem stateQDenominator_segment (g : MetricField) {w0 w1 : DarbouxState}
    (hp : statePoint w0 = statePoint w1) (sigma : ℝ) :
    stateQDenominator g (stateSegment w0 w1 sigma) =
      (1 - sigma) * stateQDenominator g w0 + sigma * stateQDenominator g w1 := by
  unfold stateQDenominator
  rw [statePoint_segment hp, ← hp]
  simp only [jetXX, jetConnection, stateGradient, stateSegment, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

theorem stateQDenominator_difference (g : MetricField) {w0 w1 : DarbouxState}
    (hp : statePoint w0 = statePoint w1) :
    stateQDenominator g w1 - stateQDenominator g w0 =
      (w1 5 - w0 5) - christoffel g 0 0 0 (statePoint w0) * (w1 2 - w0 2) -
        christoffel g 1 0 0 (statePoint w0) * (w1 3 - w0 3) := by
  simp only [stateQDenominator, ← hp, jetXX, jetConnection, stateGradient,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem stateQDenominator_segment_error (g : MetricField) {w0 w1 : DarbouxState}
    (hp : statePoint w0 = statePoint w1) {sigma B epsilon : ℝ}
    (hs : sigma ∈ Icc (0 : ℝ) 1) (hB : 0 ≤ B) (heps : 0 ≤ epsilon)
    (hGamma : ∀ r : Fin 2, |christoffel g r 0 0 (statePoint w0)| ≤ B)
    (hjet : ∀ i : Fin 6, |w1 i - w0 i| ≤ epsilon) :
    |stateQDenominator g (stateSegment w0 w1 sigma) - stateQDenominator g w0| ≤
      (1 + 2 * B) * epsilon := by
  rw [stateQDenominator_segment g hp]
  apply affine_segment_error hs (mul_nonneg (by linarith) heps)
  rw [stateQDenominator_difference g hp]
  exact three_term_jet_error hB heps (hjet 5) (hjet 2) (hjet 3) (hGamma 0) (hGamma 1)

theorem stateQDenominator_segment_lower (g : MetricField) {w0 w1 : DarbouxState}
    (hp : statePoint w0 = statePoint w1) {sigma B epsilon nu : ℝ}
    (hs : sigma ∈ Icc (0 : ℝ) 1) (hB : 0 ≤ B) (heps : 0 ≤ epsilon)
    (hGamma : ∀ r : Fin 2, |christoffel g r 0 0 (statePoint w0)| ≤ B)
    (hjet : ∀ i : Fin 6, |w1 i - w0 i| ≤ epsilon)
    (hbase : nu ≤ |stateQDenominator g w0|)
    (hsmall : (1 + 2 * B) * epsilon ≤ nu / 2) :
    nu / 2 ≤ |stateQDenominator g (stateSegment w0 w1 sigma)| :=
  denominator_lower_of_error hbase
    ((stateQDenominator_segment_error g hp hs hB heps hGamma hjet).trans hsmall)

theorem stateQDenominator_bound (g : MetricField) (w : DarbouxState) {B M : ℝ}
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hGamma : ∀ r : Fin 2, |christoffel g r 0 0 (statePoint w)| ≤ B)
    (hbox : ∀ i : Fin 6, |w i| ≤ M) :
    |stateQDenominator g w| ≤ (1 + 2 * B) * M := by
  have heq : stateQDenominator g w =
      w 5 - christoffel g 0 0 0 (statePoint w) * w 2 -
        christoffel g 1 0 0 (statePoint w) * w 3 := by
    simp only [stateQDenominator, jetXX, jetConnection, stateGradient,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [heq]
  exact three_term_jet_error hB hM (hbox 5) (hbox 2) (hbox 3) (hGamma 0) (hGamma 1)

theorem state_distance_le_of_coordinate_error {w0 w1 : DarbouxState} {epsilon : ℝ}
    (heps : 0 ≤ epsilon) (hjet : ∀ i : Fin 6, |w1 i - w0 i| ≤ epsilon) :
    ‖w1 - w0‖ ≤ epsilon := by
  apply (pi_norm_le_iff_of_nonneg heps).mpr
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using hjet i

theorem qSolutionJet_coordinate_error (z0 z : Coord → ℝ) (p : Coord) {epsilon : ℝ}
    (heps : 0 ≤ epsilon)
    (hgrad : ∀ i : Fin 2, |coordPartial i z p - coordPartial i z0 p| ≤ epsilon)
    (hmixed : |coordPartial 0 (coordPartial 1 z) p -
      coordPartial 0 (coordPartial 1 z0) p| ≤ epsilon)
    (hxx : |coordPartial 0 (coordPartial 0 z) p -
      coordPartial 0 (coordPartial 0 z0) p| ≤ epsilon) :
    ∀ i : Fin 6, |qSolutionJet z p i - qSolutionJet z0 p i| ≤ epsilon := by
  intro i
  fin_cases i
  · simpa [qSolutionJet] using heps
  · simpa [qSolutionJet] using heps
  · exact hgrad 0
  · exact hgrad 1
  · exact hmixed
  · exact hxx

theorem qHeightJetSegment_denominator_lower (g : MetricField) (z0 z : Coord → ℝ)
    (p : Coord) {sigma B epsilon nu : ℝ}
    (hs : sigma ∈ Icc (0 : ℝ) 1) (hB : 0 ≤ B) (heps : 0 ≤ epsilon)
    (hGamma : ∀ r : Fin 2, |christoffel g r 0 0 p| ≤ B)
    (hgrad : ∀ i : Fin 2, |coordPartial i z p - coordPartial i z0 p| ≤ epsilon)
    (hmixed : |coordPartial 0 (coordPartial 1 z) p -
      coordPartial 0 (coordPartial 1 z0) p| ≤ epsilon)
    (hxx : |coordPartial 0 (coordPartial 0 z) p -
      coordPartial 0 (coordPartial 0 z0) p| ≤ epsilon)
    (hbase : nu ≤ |covHessian g z0 p 0 0|)
    (hsmall : (1 + 2 * B) * epsilon ≤ nu / 2) :
    nu / 2 ≤ |stateQDenominator g (qHeightJetSegment z0 z sigma p)| := by
  apply stateQDenominator_segment_lower g
    (by simp only [statePoint_qSolutionJet]) hs hB heps
  · simpa only [statePoint_qSolutionJet] using hGamma
  · exact qSolutionJet_coordinate_error z0 z p heps hgrad hmixed hxx
  · simpa only [stateQDenominator_qSolutionJet] using hbase
  · exact hsmall

end SmoothLocal.HighEquation

end

end OAI
