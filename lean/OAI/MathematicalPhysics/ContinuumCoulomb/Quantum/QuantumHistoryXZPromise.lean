import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryXZ

namespace OAI

/-! Explicit inverse-polynomial thresholds for the actual two-local X/Z
history output. The precision is a fixed linear unary function of clock length. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory

def xzPrecision (c : QMACircuit) : ℕ := 360*(c.gates.length+1)
def xzYesThreshold (c : QMACircuit) : ℚ := 7/(20*(c.gates.length+1:ℚ))
def xzNoThreshold (c : QMACircuit) : ℚ := 23/(60*(c.gates.length+1:ℚ))

theorem xzPrecision_positive (c : QMACircuit) : 0 < xzPrecision c := by
  unfold xzPrecision
  omega

theorem xz_threshold_gap (c : QMACircuit) :
    xzNoThreshold c-xzYesThreshold c = 1/(30*(c.gates.length+1:ℚ)) := by
  have ht : (c.gates.length+1:ℚ) ≠ 0 := by positivity
  unfold xzNoThreshold xzYesThreshold
  field_simp
  ring

theorem xz_threshold_lt (c : QMACircuit) : xzYesThreshold c < xzNoThreshold c := by
  have h := xz_threshold_gap c
  have hp : (0:ℚ) < 1/(30*(c.gates.length+1:ℚ)) := by positivity
  linarith

private theorem yes_budget (c : QMACircuit) :
    1/(3*(c.gates.length+1:ℝ))+6/(xzPrecision c:ℝ) = (xzYesThreshold c:ℝ) := by
  have ht : (c.gates.length+1:ℝ) ≠ 0 := by positivity
  simp only [xzPrecision,xzYesThreshold,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    Nat.cast_ofNat,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,
    Rat.cast_one,Rat.cast_ofNat]
  field_simp
  ring

private theorem no_budget (c : QMACircuit) :
    2/(5*(c.gates.length+1:ℝ))-6/(xzPrecision c:ℝ) = (xzNoThreshold c:ℝ) := by
  have ht : (c.gates.length+1:ℝ) ≠ 0 := by positivity
  simp only [xzPrecision,xzNoThreshold,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    Nat.cast_ofNat,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,
    Rat.cast_one,Rat.cast_ofNat]
  field_simp
  ring

theorem xz_accepting (c : QMACircuit) (hT : 0 < c.gates.length) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    xzEnergy c hT (xzPrecision c) ≤ (xzYesThreshold c:ℝ) := by
  have he := (abs_le.mp (xz_accuracy c hT _ (xzPrecision_positive c))).2
  have hh := qmaOrderedHistoryModel_yes c hT hc psi hpsi hacc
  rw [← yes_budget]
  linarith

theorem xz_rejecting (c : QMACircuit) (hT : 0 < c.gates.length) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3) :
    (xzNoThreshold c:ℝ) ≤ xzEnergy c hT (xzPrecision c) := by
  have he := (abs_le.mp (xz_accuracy c hT _ (xzPrecision_positive c))).1
  have hh := qmaOrderedHistoryModel_no c hT hc hsound
  rw [← no_budget]
  linarith

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
