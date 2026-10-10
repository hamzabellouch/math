import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedReference

namespace OAI

/-! Reordering actual history terms preserves the full-space reference gap. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaOrderedReferenceTerms (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (i : Fin (qmaHistoryReferenceWork c+1)) :=
  qmaDistributedTermMatrix c τ (qmaOrderedTermEquiv c hT τ i)

theorem qmaOrderedReferenceTerms_sum (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    (∑ i, qmaOrderedReferenceTerms c hT τ i) = qmaDistributedQubitHamiltonian c τ := by
  unfold qmaOrderedReferenceTerms
  rw [(qmaOrderedTermEquiv c hT τ).sum_comp,qmaDistributedTerm_sum]

def qmaOrderedReferenceHistory (c : QMACircuit) (hT : 0 < c.gates.length)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) :
    Matrix (QMAHistoryReferenceBasis c) (QMAHistoryReferenceBasis c) ℂ :=
  qmaReferenceFamily (qmaHistoryReferenceWork c) (qmaOrderedReferenceTerms c hT τ) 1

theorem qmaOrderedReferenceHistory_lower (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < c.gates.length) (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : QMAHistoryReferenceBasis c → ℂ) :
    (2/(5*(c.gates.length+1:ℝ)))*(∑ p, Complex.normSq (u p)) ≤
      qmaQuadratic (qmaOrderedReferenceHistory c hT τ) u := by
  have hd : 0 < 5*(c.gates.length+1:ℝ) := by positivity
  have ha : (2:ℝ)/(5*(c.gates.length+1:ℝ)) ≤ 1 := by
    apply (div_le_one hd).mpr
    have : (0:ℝ) ≤ c.gates.length := Nat.cast_nonneg _
    linarith
  apply qmaReferenceFamily_lower _ _ (fun i => qmaDistributedTerm_nonnegative c τ _) _ _
    (by positivity) ha
  intro v
  change _ ≤ qmaQuadratic (∑ i, qmaOrderedReferenceTerms c hT τ i) v
  rw [qmaOrderedReferenceTerms_sum]
  exact qmaDistributedQubit_lower c hc τ hi hsound v

theorem qmaOrderedReferenceHistory_accepting (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < c.gates.length) (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    ∃ u : QMAHistoryReferenceBasis c → ℂ, (∑ p, Complex.normSq (u p)) = 1 ∧
      3*(c.gates.length+1:ℝ)*qmaQuadratic (qmaOrderedReferenceHistory c hT τ) u ≤ 1 := by
  obtain ⟨v,hv,he⟩ := qmaDistributedQubit_accepting c hc τ hi psi hpsi hacc
  refine ⟨qmaReferenceTrial (qmaHistoryReferenceWork c) v,?_,?_⟩
  · rw [qmaReferenceTrial_mass]
    exact hv
  · unfold qmaOrderedReferenceHistory
    rw [qmaReferenceTrial_energy,qmaOrderedReferenceTerms_sum]
    exact he

end ContinuumCoulomb

end

end OAI
