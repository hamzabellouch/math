import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumYYSupported
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZThirdSupported

namespace OAI

/-! Two-local X/Z reduction with a nested, explicit mediator support. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem qmaTwoLocalXZ_supported (w : κ → ι → Fin 4) (J : κ → ℝ)
    (hw : ∀ e, (qmaPauliSupport (w e)).card ≤ 2)
    (he : ∀ e, Even (qmaPauliYCount (w e))) {N : ℝ} (hN : 1 ≤ N) :
    ∃ (v : ((κ × Fin 4) × Fin 7) → ((ι ⊕ κ) ⊕ (κ × Fin 4) → Fin 4))
      (K : ((κ × Fin 4) × Fin 7) → ℝ),
      (∀ p i, v p i ≠ 2) ∧ (∀ p, (qmaPauliSupport (v p)).card ≤ 2) ∧
      (∀ p, qmaPauliSupport (v p) ⊆
        qmaMediatorSupport (qmaMediatorSupport (qmaPauliSupport (w p.1.1)) p.1.1) p.1) ∧
      |MediatorGraph.normalizedBottom (∑ p, (K p:ℂ) • qmaPauliWord (v p)) -
        MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • qmaPauliWord (w e))| ≤ 1/N := by
  have h2N : 1 ≤ 2*N := by linarith
  obtain ⟨u,L,huy,hu,hus,he₁⟩ := qmaYYReduction_supported w J hw he h2N
  obtain ⟨v,K,hvy,hv,hvs,he₂⟩ := qmaXZThird_supported u L hu huy h2N
  refine ⟨v,K,hvy,hv,?_,?_⟩
  · intro p
    exact (hvs p).trans (qmaMediatorSupport_mono (hus p.1) p.1)
  · calc
      _ ≤ |MediatorGraph.normalizedBottom (∑ p, (K p:ℂ) • qmaPauliWord (v p)) -
            MediatorGraph.normalizedBottom (∑ p, (L p:ℂ) • qmaPauliWord (u p))| +
          |MediatorGraph.normalizedBottom (∑ p, (L p:ℂ) • qmaPauliWord (u p)) -
            MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • qmaPauliWord (w e))| := abs_sub_le _ _ _
      _ ≤ 1/(2*N)+1/(2*N) := add_le_add he₂ he₁
      _ = 1/N := by ring

end ContinuumCoulomb

end

end OAI
