import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryMatrixForm

namespace OAI

/-! Normalized finite-dimensional spectral bounds for the history matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators

def qmaHistoryVector (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    EuclideanSpace ℂ (QMAHistoryBasis c) :=
  WithLp.toLp 2 (fun p => u p.1.val p.2)

theorem qmaHistoryVector_slice (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1)))
    (t : ℕ) (ht : t ≤ c.gates.length) :
    qmaHistoryFromVector c (fun p => qmaHistoryVector c u p) t = u t := by
  ext s
  simp [qmaHistoryFromVector,qmaClockIndex,qmaHistoryVector,Nat.min_eq_left ht]

theorem qmaHistoryVector_norm (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    ‖qmaHistoryVector c u‖^2 = qmaHistoryMass c u := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold qmaHistoryMass
  rw [←Fin.sum_univ_eq_sum_range,Fintype.sum_prod_type]
  simp [qmaHistoryVector,EuclideanSpace.norm_sq_eq]

theorem qmaHistoryVector_propagation (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    qmaPropagationEnergy c (qmaHistoryFromVector c (fun p => qmaHistoryVector c u p)) =
      qmaPropagationEnergy c u := by
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_range.mp ht
  rw [qmaHistoryVector_slice c u t (Nat.le_of_lt ht'),
    qmaHistoryVector_slice c u (t+1) (Nat.succ_le_of_lt ht')]

theorem qmaHistoryVector_form (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    qmaQuadratic (qmaHistoryHamiltonian c) (fun p => qmaHistoryVector c u p) =
      qmaHistoryEnergy c u := by
  rw [qmaHistoryHamiltonian_form]
  unfold qmaHistoryEnergy qmaInputPenalty qmaOutputPenalty
  rw [qmaHistoryVector_propagation,qmaHistoryVector_slice c u 0 (Nat.zero_le _),
    qmaHistoryVector_slice c u c.gates.length le_rfl]

theorem qmaQuadratic_vector_smul {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (a : ℝ) (u : ι → ℂ) :
    qmaQuadratic M ((a:ℂ) • u) = a^2*qmaQuadratic M u := by
  simp [qmaQuadratic,Matrix.mulVec_smul,star_smul,dotProduct_smul,smul_dotProduct,
    Complex.mul_re,pow_two]
  ring

theorem qmaHistoryHamiltonian_sound (c : QMACircuit) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : EuclideanSpace ℂ (QMAHistoryBasis c)) :
    2*‖u‖^2 ≤ 5*(c.gates.length+1:ℝ)*
      qmaQuadratic (qmaHistoryHamiltonian c) (fun p => u p) := by
  have h := qma_history_energy_sound c hc hsound
    (qmaHistoryFromVector c (fun p => u p))
  rw [qmaHistoryFromVector_mass,←qmaHistoryHamiltonian_form] at h
  exact h

theorem qmaHistoryHamiltonian_accepting (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    ∃ u : EuclideanSpace ℂ (QMAHistoryBasis c), ‖u‖ = 1 ∧
      3*(c.gates.length+1:ℝ)*qmaQuadratic (qmaHistoryHamiltonian c) (fun p => u p) ≤ 1 := by
  obtain ⟨u,hm,he⟩ := qma_history_accepting_witness c hc psi hpsi hacc
  let w := qmaHistoryVector c u
  have hw : 0 < ‖w‖^2 := by simpa only [w,qmaHistoryVector_norm] using hm
  have hn : ‖w‖ ≠ 0 := by intro h; rw [h] at hw; norm_num at hw
  let v := ((‖w‖⁻¹:ℝ):ℂ) • w
  have hv : ‖v‖ = 1 := by simp [v,norm_smul,hn]
  refine ⟨v,hv,?_⟩
  have hq : qmaQuadratic (qmaHistoryHamiltonian c) (fun p => v p) =
      (‖w‖⁻¹)^2*qmaQuadratic (qmaHistoryHamiltonian c) (fun p => w p) := by
    convert qmaQuadratic_vector_smul (qmaHistoryHamiltonian c) (‖w‖⁻¹) (fun p => w p) using 1
    congr 1
  have he' : 3*(c.gates.length+1:ℝ)*
      qmaQuadratic (qmaHistoryHamiltonian c) (fun p => w p) ≤ ‖w‖^2 := by
    simpa only [w,qmaHistoryVector_form,qmaHistoryVector_norm] using he
  have hm' := mul_le_mul_of_nonneg_left he' (sq_nonneg (‖w‖⁻¹))
  have hi : (‖w‖⁻¹)^2*‖w‖^2 = 1 := by field_simp
  rw [hq]
  nlinarith

end ContinuumCoulomb

end

end OAI
