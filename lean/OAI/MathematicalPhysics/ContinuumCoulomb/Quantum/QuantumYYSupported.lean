import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumYYReduction
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZSupportFactors
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZEnvelopes

namespace OAI

/-! YY elimination preserves an explicit support envelope for every emitted term. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem qmaYYReduction_supported (w : κ → ι → Fin 4) (J : κ → ℝ)
    (hw : ∀ e, (qmaPauliSupport (w e)).card ≤ 2)
    (he : ∀ e, Even (qmaPauliYCount (w e))) {N : ℝ} (hN : 1 ≤ N) :
    ∃ (v : (κ × Fin 4) → (ι ⊕ κ → Fin 4)) (K : (κ × Fin 4) → ℝ),
      (∀ p i, v p i ≠ 2) ∧ (∀ p, (qmaPauliSupport (v p)).card ≤ 3) ∧
      (∀ p, qmaPauliSupport (v p) ⊆ qmaMediatorSupport (qmaPauliSupport (w p.1)) p.1) ∧
      |MediatorGraph.normalizedBottom (∑ p, (K p:ℂ) • qmaPauliWord (v p)) -
        MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • qmaPauliWord (w e))| ≤ 1/N := by
  choose a b hsa0 hsb0 ha hb hsa hsb hfactor hcomm using
    fun e => qmaTwoLocalEvenXZ_supported (w e) (hw e) (he e)
  let R := 8*(qmaThirdBudget 0 J)^4*N
  refine ⟨fun p => qmaXZSubdivisionWord (a p.1) (b p.1) p.1 p.2,
    fun p => qmaXZSubdivisionWeight R (J p.1) p.2,?_,?_,?_,?_⟩
  · intro p i
    exact qmaXZSubdivision_noY _ _ _ (ha p.1) (hb p.1) _ _
  · intro p
    exact qmaXZSubdivision_support _ _ _ (hsa p.1) (hsb p.1) _
  · intro p
    exact qmaXZSubdivisionWord_envelope _ _ _ (hsa0 p.1) (hsb0 p.1) p.2
  · have h := qmaXZSubdivision_accuracy a b J hcomm hN
    simpa only [hfactor] using h


end ContinuumCoulomb

end

end OAI
