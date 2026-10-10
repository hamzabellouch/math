import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDistributedGap

namespace OAI

/-! The actual distributed-reference history retains the verifier promise gap. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

abbrev QMAHistoryReferenceBasis (c : QMACircuit) :=
  SourceSpinBasis (qmaHistoryReferenceWork c+1) × (QMACircuitQubit c → Fin 2)

def qmaReferenceHistory (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    Matrix (QMAHistoryReferenceBasis c) (QMAHistoryReferenceBasis c) ℂ :=
  qmaReferenceFamily (qmaHistoryReferenceWork c) (qmaHistoryReferenceTerms c τ) 1

theorem qmaReferenceHistory_lower (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : QMAHistoryReferenceBasis c → ℂ) :
    (2/(5*(c.gates.length+1:ℝ)))*(∑ p, Complex.normSq (u p)) ≤
      qmaQuadratic (qmaReferenceHistory c τ) u := by
  have hd : 0 < 5*(c.gates.length+1:ℝ) := by positivity
  have ha : (2:ℝ)/(5*(c.gates.length+1:ℝ)) ≤ 1 := by
    apply (div_le_one hd).mpr
    have : (0:ℝ) ≤ c.gates.length := Nat.cast_nonneg _
    linarith
  apply qmaReferenceFamily_lower _ _ (qmaHistoryReferenceTerms_nonnegative c τ) _ _
    (by positivity) ha
  intro v
  rw [qmaHistoryReferenceTerms_sum]
  exact qmaDistributedQubit_lower c hc τ hi hsound v

theorem qmaReferenceHistory_accepting (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    ∃ u : QMAHistoryReferenceBasis c → ℂ, (∑ p, Complex.normSq (u p)) = 1 ∧
      3*(c.gates.length+1:ℝ)*qmaQuadratic (qmaReferenceHistory c τ) u ≤ 1 := by
  obtain ⟨v,hv,he⟩ := qmaDistributedQubit_accepting c hc τ hi psi hpsi hacc
  refine ⟨qmaReferenceTrial (qmaHistoryReferenceWork c) v,?_,?_⟩
  · rw [qmaReferenceTrial_mass]
    exact hv
  · unfold qmaReferenceHistory
    rw [qmaReferenceTrial_energy,qmaHistoryReferenceTerms_sum]
    exact he

end ContinuumCoulomb

end

end OAI
