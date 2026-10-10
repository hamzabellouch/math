import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListActive
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListGraph

namespace OAI

/-! The retained part of a literal fork state has exactly the coefficient
budget and finite exchange matrix used by the parallel-fork estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram QuantumRawExchange
open scoped BigOperators Classical

def background (s : State) : List Bond := s.2.1++unpairedBonds s.2.2.2

theorem background_weights (s : State) : (background s).map (fun b => b.2.2)=retained s := by
  simp only [background,retained,List.map_append]
  congr 1
  simp only [unpairedBonds,starBonds,List.map_flatten,List.map_map,Function.comp_def]
  have h := ExactQuantumFactoring.BitStackProgram.map_range_getD s.2.2.2 []
    (fun ps => (unpaired ps).map Prod.snd)
  simpa only [groupAt,List.map_flatten,List.map_map,Function.comp_def] using
    congrArg List.flatten h

theorem rawBondMatrix_eq_bondMatrix (n : ℕ) (b : Bond) :
    rawBondMatrix n b=SourceBondLists.bondMatrix n b := by
  by_cases hi : b.1<n <;> by_cases hj : b.2.1<n <;>
    simp [rawBondMatrix,SourceBondLists.bondMatrix,hi,hj]

theorem rawMatrix_eq_matrix (n : ℕ) (bs : List Bond) (c : ℚ) :
    rawMatrix n (bs,c)=SourceBondLists.matrix n bs+(c:ℂ) • 1 := by
  have h : rawBondMatrix n=SourceBondLists.bondMatrix n :=
    funext (rawBondMatrix_eq_bondMatrix n)
  simp only [rawMatrix,h,SourceBondLists.matrix,Rat.cast_smul_eq_qsmul]

def backgroundGraph (s : State) (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) : QMARationalExchangeGraph :=
  QuantumListGraph.ofBonds s.1 (background s) s.2.2.1 hb hn

theorem background_matrix (s : State) (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) :
    qmaExchangeMatrix (backgroundGraph s hb hn).left (backgroundGraph s hb hn).right
      (fun e => ((backgroundGraph s hb hn).weight e:ℝ)) s.2.2.1 =
      rawMatrix s.1 (background s,s.2.2.1) := by
  rw [rawMatrix_eq_matrix]
  exact QuantumListGraph.ofBonds_matrix s.1 (background s) s.2.2.1 hb hn

theorem background_sum (s : State) (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (f : ℚ → ℚ) :
    (∑ e, f ((backgroundGraph s hb hn).weight e))=((retained s).map f).sum := by
  change (∑ e : Fin (background s).length, f ((background s).get e).2.2)=_
  rw [← List.sum_ofFn]
  have hl := List.ofFn_getElem_eq_map (background s) (fun b => f b.2.2)
  simp only [List.get_eq_getElem] at hl ⊢
  rw [hl]
  simpa only [List.map_map,Function.comp_def] using
    congrArg (fun xs => (xs.map f).sum) (background_weights s)

end ContinuumCoulomb.QuantumForkList

end

end OAI
