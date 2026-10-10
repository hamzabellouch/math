import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialPairs

namespace OAI

/-! Exact matrix semantics of the emitted initial singlet/port lists. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram QuantumRawExchange
open scoped BigOperators Classical

theorem initial_groupAt (n : ℕ) (bs : List Bond) (R : ℚ) (i : ℕ) (hi : i < n) :
    groupAt ((List.range n).map (initialGroup n bs R)) i=initialGroup n bs R i := by
  rw [groupAt,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem (by simpa using hi)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range]

theorem initial_active_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (R : ℚ) (f : Bond → M) :
    ((activeBonds ((List.range n).map (initialGroup n bs R))).map f).sum =
      ∑ e : Fin bs.length,
        (f (bs[e.val].1,n+2*e.val,R)+
          f (bs[e.val].2.1,n+(2*e.val+1),2*R*bs[e.val].2.2)) := by
  have hg : (List.range n).map (fun i =>
      ((groupAt ((List.range n).map (initialGroup n bs R)) i).map
        (fun p => f (i,p.1,p.2))).sum) =
      (List.range n).map (fun i => ((initialGroup n bs R i).map
        (fun p => f (i,p.1,p.2))).sum) := by
    apply List.map_congr_left
    intro i hi
    rw [initial_groupAt n bs R i (List.mem_range.mp hi)]
  simp only [activeBonds,starBonds,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def,List.length_map,List.length_range]
  rw [hg]
  exact initial_group_pair_sum n bs hb R (fun i p => f (i,p.1,p.2))

theorem initial_matrix_sum (n : ℕ) (bs : List Bond) (hb : SourceBondLists.bounded n bs)
    (c N : ℚ) :
    matrix (initial n bs c N) =
      ((List.range bs.length).map (fun e => rawBondMatrix (n+2*bs.length)
        (n+2*e,n+2*e+1,(initialScale N bs c)^2))).sum+
      (∑ e : Fin bs.length,
        (rawBondMatrix (n+2*bs.length) (bs[e.val].1,n+2*e.val,initialScale N bs c)+
          rawBondMatrix (n+2*bs.length)
            (bs[e.val].2.1,n+(2*e.val+1),2*(initialScale N bs c)*bs[e.val].2.2)))+
      (initial n bs c N).2.2.1 •
        (1 : Matrix (SourceSpinBasis (n+2*bs.length)) (SourceSpinBasis (n+2*bs.length)) ℂ) := by
  change rawMatrix (n+2*bs.length)
    ((List.range bs.length).map (fun e => (n+2*e,n+2*e+1,(initialScale N bs c)^2))++
      activeBonds ((List.range n).map (initialGroup n bs (initialScale N bs c))),
        (initial n bs c N).2.2.1)=_
  rw [rawMatrix,List.map_append,List.sum_append]
  simp only [List.map_map,Function.comp_def,initial_active_sum n bs hb]

end ContinuumCoulomb.QuantumForkList

end

end OAI
