import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedThirdSites

namespace OAI

/-! The ordered third-order gadget preserves X/Z-only input words. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedThird
open QuantumOrderedTriple
open scoped Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype κ] in
theorem output_noY (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hy : ∀ e i, w e i ≠ 2) (p : κ × Fin 7) (i : ι ⊕ κ) :
    outputWord xs w p i ≠ 2 := by
  have ha : ∀ i, first (xs p.1) (w p.1) i ≠ 2 := qmaPauliRestrict_noY _ _ (hy p.1)
  have hb : ∀ i, second (xs p.1) (w p.1) i ≠ 2 := qmaPauliRestrict_noY _ _ (hy p.1)
  have hc : ∀ i, third (xs p.1) (w p.1) i ≠ 2 := qmaPauliRestrict_noY _ _ (hy p.1)
  have hv : ∀ i, pairWord (xs p.1) (w p.1) i ≠ 2 := qmaPauliRestrict_noY _ _ (hy p.1)
  have hm : phase xs w p.1 = false := by
    simp [phase,qmaPauliYCount_zero _ ha]
  rcases p with ⟨e,k⟩
  fin_cases k <;> cases i <;>
    simp [outputWord,QuantumPolarizedThird.word,QuantumPolarizedSubdivision.axis,
      hm,qmaSinglePauliWord,ha,hb,hc,hv] <;> split_ifs <;> decide

end ContinuumCoulomb.QuantumOrderedThird

end

end OAI
