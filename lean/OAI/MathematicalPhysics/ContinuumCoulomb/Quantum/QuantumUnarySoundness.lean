import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumUnaryEnergy

namespace OAI

/-! Soundness on the entire unary-clock Hilbert space, including every
invalid clock configuration. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem qmaUnaryInvalidMass_nonneg (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) :
    0 ≤ qmaUnaryInvalidMass c u := by
  apply Finset.sum_nonneg
  intro s _
  split
  · exact le_rfl
  · exact Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _)

theorem qmaUnaryEnergy_sound (c : QMACircuit) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : QMAUnaryBasis c → ℂ) :
    2*qmaUnaryMass c u ≤ 5*(c.gates.length+1:ℝ)*qmaUnaryEnergy c u := by
  have hs := qmaCountedHistoryHamiltonian_sound c hc hsound
    (WithLp.toLp 2 (qmaUnaryRestrict c u))
  simp only [EuclideanSpace.norm_sq_eq,Complex.sq_norm] at hs
  have hb := qmaUnaryInvalidMass_le c u
  have hn := qmaUnaryInvalidMass_nonneg c u
  have hcoef : (2:ℝ) ≤ 5*(c.gates.length+1:ℝ) := by
    have h := Nat.cast_nonneg (α := ℝ) c.gates.length
    nlinarith
  have hb' : 2*qmaUnaryInvalidMass c u ≤
      5*(c.gates.length+1:ℝ)*qmaUnaryClockEnergy c u :=
    (mul_le_mul_of_nonneg_right hcoef hn).trans
      (mul_le_mul_of_nonneg_left hb (by positivity))
  have he := mul_le_mul_of_nonneg_left (qmaUnaryEnergy_restriction c u)
    (by positivity : 0 ≤ 5*(c.gates.length+1:ℝ))
  rw [qmaUnaryMass_split]
  nlinarith

end ContinuumCoulomb

end

end OAI
