import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDistributedMatrix

namespace OAI

/-! The distributed-input Hamiltonian retains the verifier's inverse-polynomial gap. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem qmaDistributedHistoryVector_energy (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    qmaDistributedHistoryEnergy c (fun i => (τ i).val)
      (qmaHistoryFromVector c (fun p => qmaHistoryVector c u p)) =
      qmaDistributedHistoryEnergy c (fun i => (τ i).val) u := by
  unfold qmaDistributedHistoryEnergy qmaOutputPenalty qmaDistributedInput
  rw [qmaHistoryVector_propagation,qmaHistoryVector_slice c u c.gates.length le_rfl]
  simp_rw [qmaHistoryVector_slice c u (τ _).val (Nat.le_of_lt_succ (τ _).isLt)]

theorem qmaUnaryDistributedHamiltonian_sound (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : EuclideanSpace ℂ (QMAUnaryBasis c)) :
    2*‖u‖^2 ≤ 5*(c.gates.length+1:ℝ)*
      qmaQuadratic (qmaUnaryDistributedHamiltonian c τ) (fun p => u p) := by
  rw [qmaUnaryDistributedHamiltonian_form,←qmaUnaryMass_norm]
  exact qmaUnaryDistributedEnergy_sound c hc τ hi hsound (fun p => u p)

theorem qmaUnaryDistributedHamiltonian_accepting (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    ∃ u : EuclideanSpace ℂ (QMAUnaryBasis c), ‖u‖ = 1 ∧
      3*(c.gates.length+1:ℝ)*
        qmaQuadratic (qmaUnaryDistributedHamiltonian c τ) (fun p => u p) ≤ 1 := by
  let v := qmaHistoryVector c (qmaIdealHistory c hc psi)
  let w : EuclideanSpace ℂ (QMAUnaryBasis c) := WithLp.toLp 2 (qmaUnaryExtend c (fun p => v p))
  have hw : ‖w‖^2 = (c.gates.length+1:ℝ) := by
    rw [←qmaUnaryMass_norm]
    change qmaUnaryMass c (qmaUnaryExtend c (fun p => v p)) = _
    rw [qmaUnaryExtend_mass]
    have hv := qmaHistoryVector_norm c (qmaIdealHistory c hc psi)
    rw [qmaIdealHistory_mass,hpsi] at hv
    simpa only [v,EuclideanSpace.norm_sq_eq,Complex.sq_norm,one_pow,mul_one] using hv
  have he : qmaQuadratic (qmaUnaryDistributedHamiltonian c τ) (fun p => w p) =
      ‖qmaRejectVector c hc psi‖^2 := by
    rw [qmaUnaryDistributedHamiltonian_form]
    change qmaUnaryDistributedEnergy c τ (qmaUnaryExtend c (fun p => v p)) = _
    rw [qmaUnaryExtend_distributed_energy]
    change qmaDistributedHistoryEnergy c (fun i => (τ i).val)
      (qmaHistoryFromVector c (fun p => qmaHistoryVector c (qmaIdealHistory c hc psi) p)) = _
    rw [qmaDistributedHistoryVector_energy,qmaIdealHistory_distributed_energy c hc τ hi]
  have hn : ‖w‖ ≠ 0 := by
    intro h
    rw [h] at hw
    have hp : (0:ℝ) < c.gates.length+1 := by positivity
    norm_num at hw
    linarith
  let u := ((‖w‖⁻¹:ℝ):ℂ) • w
  refine ⟨u,by simp [u,norm_smul,hn],?_⟩
  have hq : qmaQuadratic (qmaUnaryDistributedHamiltonian c τ) (fun p => u p) =
      (‖w‖⁻¹)^2*qmaQuadratic (qmaUnaryDistributedHamiltonian c τ) (fun p => w p) := by
    exact qmaQuadratic_vector_smul _ _ _
  have hb : 3*(c.gates.length+1:ℝ)*
      qmaQuadratic (qmaUnaryDistributedHamiltonian c τ) (fun p => w p) ≤ ‖w‖^2 := by
    rw [he,hw]
    have h := mul_le_mul_of_nonneg_left (qmaRejectVector_of_accept c hc psi hpsi hacc)
      (by positivity : 0 ≤ 3*(c.gates.length+1:ℝ))
    nlinarith
  have h := mul_le_mul_of_nonneg_left hb (sq_nonneg (‖w‖⁻¹))
  have heq : (‖w‖⁻¹)^2*‖w‖^2 = 1 := by field_simp
  rw [hq]
  nlinarith

end ContinuumCoulomb

end

end OAI
