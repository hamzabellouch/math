import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPatchPhysical
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellRouteCatalog

namespace OAI

/-! The physical output has retained edges and exactly the nine enumerated edges
at each gadget. The last perimeter edge uses the reversed catalog path. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaCrossingsEdge_cover {ν : Type*} {r : ℕ} (e : QMACrossingsGraphEdge ν r) :
    (∃ f : ν, e = .inl (.inl f)) ∨ ∃ i k, e = qmaPatchPhysicalEdge i k := by
  rcases e with (e | ⟨i,a⟩) | (i | ⟨i,a⟩)
  · exact Or.inl ⟨e,rfl⟩
  · apply Or.inr
    fin_cases a
    · exact ⟨i,5,rfl⟩
    · exact ⟨i,8,rfl⟩
    · exact ⟨i,6,rfl⟩
    · exact ⟨i,7,rfl⟩
  · exact Or.inr ⟨i,0,rfl⟩
  · apply Or.inr
    fin_cases a
    · exact ⟨i,1,rfl⟩
    · exact ⟨i,2,rfl⟩
    · exact ⟨i,3,rfl⟩
    · exact ⟨i,4,rfl⟩

def qmaPatchRoute (p : ℕ × ℕ) (k : Fin 9) : QMACellRoute :=
  ⟨.patch p k,decide (k = 8)⟩

theorem qmaPatchRoute_source (p : ℕ × ℕ) (k : Fin 9) :
    (qmaPatchRoute p k).source = qmaPatchTranslate p (qmaCrossingPatchVertex (qmaPatchSource k)) := by
  by_cases h : k = 8 <;>
    simp [qmaPatchRoute,QMACellRoute.source,QMACellRouteBody.source,QMACellRouteBody.target,qmaPatchSource,h]

theorem qmaPatchRoute_target (p : ℕ × ℕ) (k : Fin 9) :
    (qmaPatchRoute p k).target = qmaPatchTranslate p (qmaCrossingPatchVertex (qmaPatchTarget k)) := by
  by_cases h : k = 8 <;>
    simp [qmaPatchRoute,QMACellRoute.target,QMACellRouteBody.source,QMACellRouteBody.target,qmaPatchTarget,h]

end ContinuumCoulomb

end

end OAI
