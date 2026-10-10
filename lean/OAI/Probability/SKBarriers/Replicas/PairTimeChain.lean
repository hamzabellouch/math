import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFPartitionRepresentation
import OAI.Probability.SKBarriers.Replicas.PairFinitePressure
import OAI.Probability.SKBarriers.Hierarchy.TimeChainPressureAlgebra

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem sum_append_before (a b : ℕ) (f : Fin a → ℝ) (g : Fin b → ℝ) :
    (∑ j : Fin (a+b), if j.val<a then Fin.append f g j else 0)=∑ i, f i := by
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd,Fin.val_natAdd,Fin.append_left,Fin.append_right]
  simp only [Fin.is_lt,ite_true,Nat.not_lt.mpr (Nat.le_add_right _ _),ite_false,Finset.sum_const_zero,add_zero]

theorem pairConstrainedPressure_twoChains {N : ℕ} (hN : 0<N) (a b : ℕ) (β : ℝ)
    (l : Fin (a+1) → ℝ × ℝ≥0) (r : Fin (b+1) → ℝ × ℝ≥0)
    (hm0 : (l 0).1=0) (ht0 : (l 0).2=0)
    (hm : ∀ i, (Fin.append l r i).1∈Icc (0:ℝ) 1)
    (hmono : Monotone (fun i => (Fin.append l r i).1))
    (ht : (∑ i, ((l i).2:ℝ))+(∑ i, ((r i).2:ℝ))=1)
    (hD : Nonempty (MatrixStates N 2 (pairMatrix 1 (∑ i, ((l i).2:ℝ))))) :
    matrixConstrainedPressure N 2 β (pairMatrix 1 (∑ i, ((l i).2:ℝ))) ≤
      2*(scalarTimeChain β (List.ofFn l++List.ofFn r) scalarSpinTerminal 0-
        β^2/4*chainQuadraticPenalty 0 (List.ofFn l++List.ofFn r))-
      (scalarTimeChainAverage β (List.ofFn l) (scalarTimeChain β (List.ofFn r) scalarSpinTerminal)
        (fun x => (scalarTimeChainAverage β (List.ofFn r) scalarSpinTerminal scalarMagnetization x)^2) 0-
        (∑ i, ((l i).2:ℝ)))^2/2 := by
  let p := Fin.append l r
  let c (i : Fin ((a+1)+b+1)) := Real.sqrt ((p i).2:ℝ)
  have hc (i) : (c i)^2=((p i).2:ℝ) := Real.sq_sqrt (p i).2.coe_nonneg
  have hsum : ∑ i, (c i)^2=1 := by
    simp only [hc]
    change (∑ i : Fin ((a+1)+(b+1)), ((Fin.append l r i).2:ℝ))=1
    rw [Fin.sum_univ_add]
    simpa only [Fin.append_left,Fin.append_right] using ht
  have hq : (∑ i : Fin ((a+1)+b+1), if i.val<a+1 then (c i)^2 else 0)=∑ i, ((l i).2:ℝ) := by
    simp only [hc]
    change (∑ i : Fin ((a+1)+(b+1)), if i.val<a+1 then ((Fin.append l r i).2:ℝ) else 0)=_
    rw [Fin.sum_univ_add]
    simp only [Fin.val_castAdd,Fin.val_natAdd,Fin.append_left,Fin.append_right]
    simp only [Fin.is_lt,ite_true,Nat.not_lt.mpr (Nat.le_add_right _ _),ite_false,Finset.sum_const_zero,add_zero]
  have H := pairConstrainedPressure_finite hN (a+1) b β (fun i => (p i).1) c
    (by simpa only [p,show (0 : Fin ((a+1)+(b+1)))=(0:Fin (a+1)).castAdd (b+1) from rfl,Fin.append_left] using hm0) hm hmono hsum (by simpa only [hq] using hD)
  dsimp only at H
  rw [hq] at H
  have hp0 : (p 0).2=0 := by simpa only [p,show (0 : Fin ((a+1)+(b+1)))=(0:Fin (a+1)).castAdd (b+1) from rfl,Fin.append_left] using ht0
  have HP := chainQuadraticPenalty_ofFn_zero ((a+1)+b) p hp0
  change chainQuadraticPenalty 0 (List.ofFn (Fin.append l r))=_ at HP
  rw [List.ofFn_fin_append] at HP
  simp only [hc] at H
  rw [← HP] at H
  have HV : scalarTimeChain β (List.ofFn l++List.ofFn r) scalarSpinTerminal=
      scalarHierarchy ((a+1)+b+1) (fun i => (p i).1) (fun i => β*c i) scalarSpinTerminal := by
    rw [← List.ofFn_fin_append]
    exact scalarTimeChain_ofFn β _ _ _ _
  rw [← HV] at H
  have HG : scalarMomentSquare ((a+1)+b+1) (fun i => (p i).1) (fun i => β*c i)
      scalarSpinTerminal scalarMagnetization ⟨a+1,by omega⟩=
      scalarTimeChainAverage β (List.ofFn l) (scalarTimeChain β (List.ofFn r) scalarSpinTerminal)
        (fun x => (scalarTimeChainAverage β (List.ofFn r) scalarSpinTerminal scalarMagnetization x)^2) := by
    change scalarMomentSquare ((a+1)+(b+1)) (fun i => (p i).1)
      (fun i => β*Real.sqrt ((p i).2:ℝ)) scalarSpinTerminal scalarMagnetization ⟨a+1,by omega⟩=_
    rw [scalarMomentSquare_split (a+1) (b+1)]
    simp only [p,Fin.append_left,Fin.append_right]
    rw [scalarTimeChain_ofFn,scalarTimeChainAverage_ofFn,scalarTimeChainAverage_ofFn]
  rw [HG] at H
  exact H

end SK.Analytic

end
end

end OAI
