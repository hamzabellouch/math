import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRebitSoundness

namespace OAI

/-! An entirely real circuit Hamiltonian with the same verified promise gap. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

abbrev QMARealBasis (c : QMACircuit) := Fin 2 × QMAUnaryBasis c

def qmaRealHamiltonian (c : QMACircuit) : Matrix (QMARealBasis c) (QMARealBasis c) ℂ :=
  qmaRebitMatrix (qmaUnaryHamiltonian c)

theorem qmaRealHamiltonian_hermitian (c : QMACircuit) : (qmaRealHamiltonian c).IsHermitian :=
  qmaRebitMatrix_hermitian _ (qmaUnaryHamiltonian_hermitian c)

theorem qmaRealHamiltonian_real (c : QMACircuit) (p q : QMARealBasis c) :
    (qmaRealHamiltonian c p q).im = 0 := qmaRebitMatrix_real _ p q

theorem qmaRealHamiltonian_sound (c : QMACircuit) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : EuclideanSpace ℂ (QMARealBasis c)) :
    2*‖u‖^2 ≤ 5*(c.gates.length+1:ℝ)*
      qmaQuadratic (qmaRealHamiltonian c) (fun p => u p) := by
  have hA (v : QMAUnaryBasis c → ℂ) :
      2*(∑ p, Complex.normSq (v p)) ≤ 5*(c.gates.length+1:ℝ)*
        qmaQuadratic (qmaUnaryHamiltonian c) v := by
    have h := qmaUnaryHamiltonian_sound c hc hsound (WithLp.toLp 2 v)
    simpa only [EuclideanSpace.norm_sq_eq,Complex.sq_norm,PiLp.toLp_apply] using h
  have h := qmaRebitMatrix_lower (qmaUnaryHamiltonian c) 2
    (5*(c.gates.length+1:ℝ)) hA (fun p => u p)
  simpa only [EuclideanSpace.norm_sq_eq,Complex.sq_norm,qmaRealHamiltonian] using h

theorem qmaRealHamiltonian_accepting (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    ∃ u : EuclideanSpace ℂ (QMARealBasis c), ‖u‖ = 1 ∧
      3*(c.gates.length+1:ℝ)*qmaQuadratic (qmaRealHamiltonian c) (fun p => u p) ≤ 1 := by
  obtain ⟨v,hv,he⟩ := qmaUnaryHamiltonian_accepting c hc psi hpsi hacc
  let u : EuclideanSpace ℂ (QMARealBasis c) := WithLp.toLp 2 (qmaRebitVector (fun p => v p))
  have hu : ‖u‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mp
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ p, ‖qmaRebitVector (fun p => v p) p‖^2) = 1^2
    simp only [Complex.sq_norm]
    rw [qmaRebitVector_mass]
    have hv2 : ‖v‖^2 = (1:ℝ)^2 := by rw [hv]
    rw [EuclideanSpace.norm_sq_eq] at hv2
    simpa only [Complex.sq_norm] using hv2
  refine ⟨u,hu,?_⟩
  change 3*(c.gates.length+1:ℝ)*qmaQuadratic (qmaRebitMatrix (qmaUnaryHamiltonian c))
    (qmaRebitVector (fun p => v p)) ≤ 1
  rw [qmaRebitMatrix_quadratic]
  exact he

theorem qmaRealBasis_card (c : QMACircuit) :
    Fintype.card (QMARealBasis c) = 2^(c.gates.length+c.work+4) := by
  calc
    Fintype.card (QMARealBasis c) = 2*Fintype.card (QMAUnaryBasis c) := by
      rw [Fintype.card_prod,Fintype.card_fin]
    _ = 2*2^(c.gates.length+c.work+3) := by rw [qmaUnaryBasis_card]
    _ = 2^(c.gates.length+c.work+3)*2 := mul_comm _ _
    _ = 2^((c.gates.length+c.work+3)+1) := (pow_succ _ _).symm
    _ = 2^(c.gates.length+c.work+4) := by congr 1

end ContinuumCoulomb

end

end OAI
