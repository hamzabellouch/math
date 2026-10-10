import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourAxis

namespace OAI

/-! Calibration of the physical inter-block strength for either coupling sign. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourCouplingSign (j : ℝ) : Bool := decide (j ≤ 0)

def qmaFourCouplingSize (a b : Fin 2) (j : ℝ) : ℝ :=
  Real.sqrt (8*|j|/(3*qmaFourAxisScale a*qmaFourAxisScale b))

theorem qmaFourCouplingSize_nonneg (a b : Fin 2) (j : ℝ) : 0 ≤ qmaFourCouplingSize a b j :=
  Real.sqrt_nonneg _

theorem qmaFourCouplingSize_square (a b : Fin 2) (j : ℝ) :
    (3/8:ℝ)*(qmaFourCouplingSize a b j)^2*qmaFourAxisScale a*qmaFourAxisScale b = |j| := by
  have ha := qmaFourAxisScale_pos a
  have hb := qmaFourAxisScale_pos b
  have hane : qmaFourAxisScale a ≠ 0 := ne_of_gt ha
  have hbne : qmaFourAxisScale b ≠ 0 := ne_of_gt hb
  have hden : 0 < 3*qmaFourAxisScale a*qmaFourAxisScale b := by positivity
  have hnon : 0 ≤ 8*|j|/(3*qmaFourAxisScale a*qmaFourAxisScale b) := by positivity
  rw [qmaFourCouplingSize,Real.sq_sqrt hnon]
  field_simp

theorem qmaFourCouplingSign_calibration (a b : Fin 2) (j : ℝ) :
    -(3/8:ℝ)*(qmaFourCouplingSize a b j)^2*qmaFourAxisScale a*
      (qmaFourAxisSign (qmaFourCouplingSign j)*qmaFourAxisScale b) = j := by
  have he := qmaFourCouplingSize_square a b j
  calc
    _ = -((3/8:ℝ)*(qmaFourCouplingSize a b j)^2*qmaFourAxisScale a*qmaFourAxisScale b)*
        qmaFourAxisSign (qmaFourCouplingSign j) := by ring
    _ = -|j| *qmaFourAxisSign (qmaFourCouplingSign j) := by rw [he]
    _ = j := by
      by_cases hj : j ≤ 0
      · simp [qmaFourAxisSign,qmaFourCouplingSign,hj,abs_of_nonpos hj]
      · simp [qmaFourAxisSign,qmaFourCouplingSign,hj,abs_of_pos (lt_of_not_ge hj)]

end ContinuumCoulomb

end

end OAI
