import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialExchangeModel

namespace OAI

/-! The full verifier promise is preserved by a bounded-density rational exchange family. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem QMASpatialExchangeModel.qubits_bound {A B : ℕ} (M : QMASpatialExchangeModel A B) :
    M.n ≤ (M.rows+1)*(M.width+1)*A := by
  simpa only [Fintype.card_fin] using qmaGrid_density_card M.cell M.qubitDensity

theorem QMASpatialExchangeModel.incidence_bound {A B : ℕ} (M : QMASpatialExchangeModel A B)
    (q : Fin M.n) :
    (Finset.univ.filter (fun e => q = M.left e ∨ q = M.right e)).card ≤ 9*B := by
  have h := qmaGrid_incidence_bound M.cell M.anchor (fun e => {M.left e,M.right e})
    (by
      intro e i hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact (M.geometry e).1
      · exact (M.geometry e).2) M.termDensity q
  simpa only [Finset.mem_insert,Finset.mem_singleton] using h

theorem qmaCircuit_spatial_exchange (c : QMACircuit) (hc : c.WellFormed)
    (N : ℕ) (hN : 0 < N) :
    ∃ G : QMASpatialExchangeModel
        (4*(qmaVerifierSpatialQubits+qmaVerifierSpatialTerms))
        (6*(qmaVerifierSpatialQubits+qmaVerifierSpatialTerms)+25*(4*qmaVerifierSpatialTerms)),
      G.rows = (qmaNearestCircuit (qmaNonemptyCircuit c)).gates.length ∧ G.width = c.work ∧
      (∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness), ‖psi‖ = 1 →
        2/3 ≤ qmaAcceptance c hc psi →
        G.energy ≤ 1/(3*((qmaSparseCircuit (qmaNonemptyCircuit c)).gates.length+1:ℝ))+1/(N:ℝ)) ∧
      ((∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness), ‖psi‖ = 1 →
        qmaAcceptance c hc psi ≤ 1/3) →
        2/(5*((qmaSparseCircuit (qmaNonemptyCircuit c)).gates.length+1:ℝ))-1/(N:ℝ) ≤ G.energy) := by
  obtain ⟨M,hr,hw,_hcoeff,hp,hy,hn⟩ := qmaCircuit_spatial_rational_private c hc (3*N) (by omega)
  obtain ⟨G,hGr,hGw,he⟩ := M.toExchange hp (3*N) (by omega)
  simp only [Nat.cast_mul,Nat.cast_ofNat] at he hy hn
  refine ⟨G,hGr.trans hr,hGw.trans hw,?_,?_⟩
  · intro psi hpsi ha
    have h := hy psi hpsi ha
    have hle := (abs_le.mp he).2
    have hsum : 1/(3*N:ℝ)+2/(3*N:ℝ) = 1/(N:ℝ) := by ring
    linarith
  · intro hs
    have h := hn hs
    have hle := (abs_le.mp he).1
    have hsum : 1/(3*N:ℝ)+2/(3*N:ℝ) = 1/(N:ℝ) := by ring
    linarith

end ContinuumCoulomb

end

end OAI
