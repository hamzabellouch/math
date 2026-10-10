import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSelectProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSelectionUnique
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingListActual

namespace OAI

/-! The finite endpoint scans recover the actual selected rational couplings.
No matrix or energy comparison is assumed by this source-data bridge. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open QuantumCrossingListBlock
open scoped BigOperators Classical

def encodedSites {n r : ℕ} (site : Fin r → Fin 4 → Fin n) (i : Fin r) : Sites :=
  (((site i 0).val,(site i 1).val),((site i 2).val,(site i 3).val))

theorem terminalPair_encoded {n r : ℕ} (site : Fin r → Fin 4 → Fin n)
    (i : Fin r) (a : Fin 2) :
    terminalPair a (encodedSites site i)=
      ((site i (if a=0 then 0 else 1)).val,(site i (if a=0 then 2 else 3)).val) := by
  fin_cases a <;> rfl

theorem hits_selected {G : QMARationalExchangeGraph} {r : ℕ}
    (S : QMARationalCrossingSelection G r)
    (htag : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a))
    (e : G.Edge) (i : Fin r) (a : Fin 2) :
    hits (((G.left e).val,(G.right e).val,G.weight e),terminalPair a (encodedSites S.site i)) =
      decide (S.tag e=some (i,a)) := by
  apply Bool.eq_iff_iff.mpr
  rw [hits_iff,decide_eq_true_eq,htag,terminalPair_encoded]
  simp only [QMARationalExchangeGraph.CrossingMatch,Prod.mk.injEq,Fin.ext_iff]
  tauto

theorem weight_selected {G : QMARationalExchangeGraph} {r : ℕ}
    (S : QMARationalCrossingSelection G r)
    (htag : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a))
    {m : ℕ} (labels : G.Edge ≃ Fin m) (i : Fin r) (a : Fin 2) :
    weight (QuantumListGraph.packed G labels,terminalPair a (encodedSites S.site i))=
      S.weight (i,a) := by
  simp only [weight,QuantumListGraph.packed,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,contribution,hits_selected S htag,decide_eq_true_eq]
  unfold QMARationalCrossingSelection.weight
  rw [qmaSumSubtypePredicate]
  exact labels.symm.sum_comp (fun e => if S.tag e=some (i,a) then G.weight e else 0)

theorem crossings_selected {G : QMARationalExchangeGraph} {r : ℕ}
    (S : QMARationalCrossingSelection G r)
    (htag : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a))
    {m : ℕ} (labels : G.Edge ≃ Fin m) :
    crossings (QuantumListGraph.packed G labels,List.ofFn (encodedSites S.site))=
      List.ofFn (QuantumCrossingListLayer.actualCrossing S.layer) := by
  simp only [crossings,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Prod.ext
  · exact Prod.ext (weight_selected S htag labels i 0) (weight_selected S htag labels i 1)
  · rfl

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
