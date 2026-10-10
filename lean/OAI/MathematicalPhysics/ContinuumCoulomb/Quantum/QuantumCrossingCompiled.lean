import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingRetention
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingListMatrix

namespace OAI

/-! Full-space correctness of the computed crossing transformation, starting
from an ordinary finite bond tape and its selected physical terminals. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open QuantumCrossingListBlock
open scoped Classical

variable {G : QMARationalExchangeGraph} {r : ℕ}
    (S : QMARationalCrossingSelection G r) {m : ℕ} (labels : G.Edge ≃ Fin m)

def retainedGraph : QMARationalExchangeGraph :=
  QuantumListGraph.ofBonds G.n
    (retained (pairs (List.ofFn (encodedSites S.site)),QuantumListGraph.packed G labels))
    G.constant
    (retained_bounded _ _ (QuantumListGraph.packed_bounded G labels))
    (retained_noLoops _ _ (QuantumListGraph.packed_noLoops G labels))

def computedLayer : QMARationalCrossingLayer r where
  base := retainedGraph S labels
  site := S.site
  injective := S.injective
  J i := weight (QuantumListGraph.packed G labels,terminalPair 0 (encodedSites S.site i))
  K i := weight (QuantumListGraph.packed G labels,terminalPair 1 (encodedSites S.site i))

private theorem packed_ofBonds (n : ℕ) (xs : List MediatorListProgram.Bond) (c : ℚ)
    (hb : SourceBondLists.bounded n xs) (hn : ∀ e ∈ xs, e.1 ≠ e.2.1) :
    QuantumListGraph.packed (QuantumListGraph.ofBonds n xs c hb hn) (Equiv.refl _)=xs := by
  change List.ofFn (fun i : Fin xs.length => xs.get i)=xs
  exact List.ofFn_get xs

theorem compiled_packet (N : ℚ) :
    value (N,(G.n,QuantumListGraph.packed G labels,G.constant),
      List.ofFn (encodedSites S.site)) =
      QuantumCrossingListLayer.actualInput (computedLayer S labels) N (Equiv.refl _) := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact (packed_ofBonds G.n
            (retained (pairs (List.ofFn (encodedSites S.site)),QuantumListGraph.packed G labels))
            G.constant (retained_bounded _ _ (QuantumListGraph.packed_bounded G labels))
            (retained_noLoops _ _ (QuantumListGraph.packed_noLoops G labels))).symm
        · rfl
  · simp only [value,crossings,QuantumCrossingListLayer.actualInput,List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    rfl

variable (htag : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a))
include htag

theorem retainedGraph_matrix :
    qmaExchangeMatrix (retainedGraph S labels).left (retainedGraph S labels).right
      (fun e => ((retainedGraph S labels).weight e:ℝ)) (retainedGraph S labels).constant =
      qmaExchangeMatrix S.retained.left S.retained.right
        (fun e => (S.retained.weight e:ℝ)) S.retained.constant := by
  exact (QuantumListGraph.ofBonds_matrix G.n
    (retained (pairs (List.ofFn (encodedSites S.site)),QuantumListGraph.packed G labels))
    G.constant (retained_bounded _ _ (QuantumListGraph.packed_bounded G labels))
    (retained_noLoops _ _ (QuantumListGraph.packed_noLoops G labels))).trans
      (retained_matrix S htag labels)

theorem computedLayer_source_matrix :
    qmaExchangeMatrix (computedLayer S labels).source.left (computedLayer S labels).source.right
      (fun e => ((computedLayer S labels).source.weight e:ℝ))
      (computedLayer S labels).source.constant =
      qmaExchangeMatrix G.left G.right (fun e => (G.weight e:ℝ)) G.constant := by
  apply (QMARationalCrossingLayer.source_matrix (computedLayer S labels)).trans
  apply Eq.trans _ ((S.layer.source_matrix).symm.trans S.source_matrix)
  apply congrArg₂ (fun a b : Matrix (SourceSpinBasis G.n) (SourceSpinBasis G.n) ℂ => a+b)
  · exact retainedGraph_matrix S labels htag
  · apply Finset.sum_congr rfl
    intro i _
    change
      (weight (QuantumListGraph.packed G labels,terminalPair 0 (encodedSites S.site i)):ℂ) •
          sourceHeisenbergMatrix G.n (S.site i 0) (S.site i 2) +
        (weight (QuantumListGraph.packed G labels,terminalPair 1 (encodedSites S.site i)):ℂ) •
          sourceHeisenbergMatrix G.n (S.site i 1) (S.site i 3) = _
    rw [weight_selected S htag,weight_selected S htag]
    rfl

theorem computedLayer_source_energy : (computedLayer S labels).source.energy=G.energy := by
  exact congrArg (sourceMatrixBottom G.n) (computedLayer_source_matrix S labels htag)

theorem compiled_energy_error {N : ℚ} (hN : 0 < N) :
    |(QuantumCrossingListLayer.actualGraph (computedLayer S labels) N (Equiv.refl _)).energy-
        G.energy| ≤ 1/(N:ℝ) := by
  rw [← computedLayer_source_energy S labels htag]
  exact QuantumCrossingListLayer.energy_error (computedLayer S labels) hN (Equiv.refl _)

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
