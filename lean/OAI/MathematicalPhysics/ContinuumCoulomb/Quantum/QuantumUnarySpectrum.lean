import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumUnaryMatrix

namespace OAI

/-! The full qubit-space history Hamiltonian has a strict inverse-polynomial
promise gap. No restriction to the valid clock subspace is assumed. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem qmaUnaryMass_norm (c : QMACircuit) (u : EuclideanSpace ℂ (QMAUnaryBasis c)) :
    qmaUnaryMass c (fun p => u p) = ‖u‖^2 := by
  simp only [qmaUnaryMass,EuclideanSpace.norm_sq_eq,Complex.sq_norm]

theorem qmaUnaryHamiltonian_sound (c : QMACircuit) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : EuclideanSpace ℂ (QMAUnaryBasis c)) :
    2*‖u‖^2 ≤ 5*(c.gates.length+1:ℝ)*
      qmaQuadratic (qmaUnaryHamiltonian c) (fun p => u p) := by
  rw [qmaUnaryHamiltonian_form,←qmaUnaryMass_norm]
  exact qmaUnaryEnergy_sound c hc hsound (fun p => u p)

theorem qmaUnaryHamiltonian_accepting (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    ∃ u : EuclideanSpace ℂ (QMAUnaryBasis c), ‖u‖ = 1 ∧
      3*(c.gates.length+1:ℝ)*qmaQuadratic (qmaUnaryHamiltonian c) (fun p => u p) ≤ 1 := by
  obtain ⟨v,hv,he⟩ := qmaCountedHistoryHamiltonian_accepting c hc psi hpsi hacc
  let u : EuclideanSpace ℂ (QMAUnaryBasis c) := WithLp.toLp 2 (qmaUnaryExtend c (fun p => v p))
  have hu : ‖u‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mp
    rw [←qmaUnaryMass_norm]
    change qmaUnaryMass c (qmaUnaryExtend c (fun p => v p)) = 1^2
    rw [qmaUnaryExtend_mass]
    have hv2 : ‖v‖^2 = (1:ℝ)^2 := by rw [hv]
    rw [EuclideanSpace.norm_sq_eq] at hv2
    simpa only [Complex.sq_norm] using hv2
  refine ⟨u,hu,?_⟩
  rw [qmaUnaryHamiltonian_form]
  change 3*(c.gates.length+1:ℝ)*qmaUnaryEnergy c (qmaUnaryExtend c (fun p => v p)) ≤ 1
  rw [qmaUnaryExtend_energy]
  exact he

theorem qmaUnaryBasis_card (c : QMACircuit) :
    Fintype.card (QMAUnaryBasis c) = 2^(c.gates.length+c.work+3) := by
  simp only [QMAUnaryBasis,SourceSpinBasis,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
  rw [←pow_add]
  congr 1
  omega

end ContinuumCoulomb

end

end OAI
