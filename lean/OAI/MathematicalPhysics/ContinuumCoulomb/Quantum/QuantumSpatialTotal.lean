import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCircuitPadding
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialPrivate
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialRational

namespace OAI

/-! Every verifier circuit admits a spatial private-pair X/Z family with rational coefficients. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

abbrev qmaVerifierSpatialQubits : ℕ := 45+1077940224*64+80*(7516192768*64)
abbrev qmaVerifierSpatialTerms : ℕ := 448*(7516192768*64)

theorem qmaCircuit_spatial_XZ_total (c : QMACircuit) (hc : c.WellFormed)
    {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : QMASpatialXZModel qmaVerifierSpatialQubits qmaVerifierSpatialTerms,
      G.rows = (qmaNearestCircuit (qmaNonemptyCircuit c)).gates.length ∧ G.width = c.work ∧
      (∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness), ‖psi‖ = 1 →
        2/3 ≤ qmaAcceptance c hc psi →
        G.toQMAXZModel.energy ≤
          1/(3*((qmaSparseCircuit (qmaNonemptyCircuit c)).gates.length+1:ℝ))+1/N) ∧
      ((∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness), ‖psi‖ = 1 →
        qmaAcceptance c hc psi ≤ 1/3) →
        2/(5*((qmaSparseCircuit (qmaNonemptyCircuit c)).gates.length+1:ℝ))-1/N ≤
          G.toQMAXZModel.energy) := by
  obtain ⟨G,hr,hw,hy,hn⟩ := qmaCircuit_spatial_XZ (qmaNonemptyCircuit c)
    (qmaNonemptyCircuit_wellFormed c hc) (qmaNonemptyCircuit_sparse_pos c)
    (qmaNonemptyCircuit_nearest c) hN
  refine ⟨G,hr,hw,?_,?_⟩
  · intro psi hpsi ha
    apply hy psi hpsi
    rwa [qmaNonemptyCircuit_acceptance]
  · intro hs
    apply hn
    intro psi hpsi
    rw [qmaNonemptyCircuit_acceptance c hc psi]
    exact hs psi hpsi

theorem qmaCircuit_spatial_rational_private (c : QMACircuit) (hc : c.WellFormed)
    (N : ℕ) (hN : 0 < N) :
    ∃ G : QMASpatialXZModel (qmaVerifierSpatialQubits+qmaVerifierSpatialTerms)
        (4*qmaVerifierSpatialTerms),
      G.rows = (qmaNearestCircuit (qmaNonemptyCircuit c)).gates.length ∧ G.width = c.work ∧
      (∀ e, ∃ r : ℚ, G.coefficient e = r) ∧
      (∀ p q, (qmaPauliSupport (G.word p)).card = 2 →
        qmaPauliSupport (G.word p) = qmaPauliSupport (G.word q) → p = q) ∧
      (∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness), ‖psi‖ = 1 →
        2/3 ≤ qmaAcceptance c hc psi →
        G.toQMAXZModel.energy ≤
          1/(3*((qmaSparseCircuit (qmaNonemptyCircuit c)).gates.length+1:ℝ))+1/(N:ℝ)) ∧
      ((∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness), ‖psi‖ = 1 →
        qmaAcceptance c hc psi ≤ 1/3) →
        2/(5*((qmaSparseCircuit (qmaNonemptyCircuit c)).gates.length+1:ℝ))-1/(N:ℝ) ≤
          G.toQMAXZModel.energy) := by
  have h3N : 1 ≤ (3*N:ℕ) := by omega
  have h3NR : 1 ≤ (3*N:ℝ) := by exact_mod_cast h3N
  obtain ⟨M,hr,hw,hy,hn⟩ := qmaCircuit_spatial_XZ_total c hc h3NR
  obtain ⟨P,hp,he,hPr,hPw⟩ := M.private h3NR
  let m := (Fintype.card P.Term+1)*(3*N)
  let G := P.withCoefficients (fun e => (qmaRationalRound m (P.coefficient e):ℝ))
  have hg : |G.toQMAXZModel.energy-P.toQMAXZModel.energy| ≤ 1/(3*N:ℝ) := by
    have h := P.round_energy (3*N) (by omega)
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using h
  refine ⟨G,hPr.trans hr,hPw.trans hw,?_,hp,?_,?_⟩
  · intro e
    exact ⟨qmaRationalRound m (P.coefficient e),rfl⟩
  · intro psi hpsi ha
    have h := hy psi hpsi ha
    have he' := (abs_le.mp he).2
    have hg' := (abs_le.mp hg).2
    have hsum : 1/(3*N:ℝ)+1/(3*N:ℝ)+1/(3*N:ℝ) = 1/(N:ℝ) := by ring
    linarith
  · intro hs
    have h := hn hs
    have he' := (abs_le.mp he).1
    have hg' := (abs_le.mp hg).1
    have hsum : 1/(3*N:ℝ)+1/(3*N:ℝ)+1/(3*N:ℝ) = 1/(N:ℝ) := by ring
    linarith

end ContinuumCoulomb

end

end OAI
