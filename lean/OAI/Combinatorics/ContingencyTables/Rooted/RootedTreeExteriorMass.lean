import OAI.Combinatorics.ContingencyTables.Rooted.RootedTreeBounds
import OAI.Combinatorics.ContingencyTables.Rooted.RootedTreeFeasibleMass
import OAI.Combinatorics.ContingencyTables.Rooted.RootedPhysicalNormalizer
import OAI.Combinatorics.ContingencyTables.Rooted.TreeExteriorPositions

namespace OAI

/-! # Selected-root exterior fibres normalized by their actual physical mass -/

namespace ContingencyTables.RootedTreeMarginal

open scoped BigOperators Classical
open CompanionFactorialApplication RootedPhysicalNormalizer BalancedCellFibres
open ForestPenaltyApplication ForestLiteralCount
open TreeMarginalSignature (cellWidth)

variable {I J : Type*} [Fintype I] [Fintype J]

lemma scalar_sum_eq_physicalMass (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J) :
    (∑ q ∈ Finset.range (cellWidth A t+1),scalarExact A R alpha t q)=physicalMass A R alpha := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [exact_eq_fibre]
  exact sum_fibre (cellWidth A)
    (RootedPenalty.physicalWeight A R alpha) t

/-- A lower exterior tree position is controlled by the actual feasible
table attaining its upper bound, exactly as in the manuscript. -/
theorem lower_exterior_point (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ht : A.T.Adj (.inl t.1) (.inr t.2)) (ha : 0 ≤ alpha)
    (hW : 20*A.d ≤ A.W) (B K : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K) (hK : 0 < K)
    (Y : I → J → ℤ) (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j)
    (hr : ∀ i,(∑ j,Y i j)=A.r i) (hc : ∀ j,(∑ i,Y i j)=A.c j)
    (hy : Y t.1 t.2=(A.b t.1 t.2:ℤ)) (k : ℕ) (hk : k < 10*A.d*A.b t.1 t.2) :
    scalarExact A R alpha t k/physicalMass A R alpha ≤ (2*K:ℝ)/A.b t.1 t.2 := by
  let N := 10*A.d*A.b t.1 t.2+A.b t.1 t.2-k
  have hb : 0 < A.b t.1 t.2 := by have h := (A.hlarge _ _ (A.hTG ht)).2; omega
  have hend := upper_tree_endpoint A R alpha t ht Y hY hr hc hy
  have hkN : k+N=10*A.d*A.b t.1 t.2+A.b t.1 t.2 := by dsimp only [N]; omega
  have hwidth : cellWidth A t=20*A.d*A.b t.1 t.2 := by simp only [cellWidth,width,ht,ite_true]
  have hprod : A.b t.1 t.2 ≤ A.d*A.b t.1 t.2 := by have hd := A.hd; nlinarith
  have hh := scalar_exact_forward_point_bound A R alpha t ha hW B K k N (A.b t.1 t.2) hB hBK hK
    (by dsimp only [N]; omega) hb (by dsimp only [N]; omega)
    (by rw [hkN,hwidth]; nlinarith) (by rw [hkN]; exact hend)
  rwa [scalar_sum_eq_physicalMass] at hh

theorem upper_exterior_point (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ht : A.T.Adj (.inl t.1) (.inr t.2)) (ha : 0 ≤ alpha)
    (hW : 20*A.d ≤ A.W) (B K : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K) (hK : 0 < K)
    (Y : I → J → ℤ) (hY : ∀ i j,0 ≤ Y i j ∧ Y i j ≤ A.b i j)
    (hr : ∀ i,(∑ j,Y i j)=A.r i) (hc : ∀ j,(∑ i,Y i j)=A.c j)
    (hy : Y t.1 t.2=0) (k : ℕ)
    (hk : 10*A.d*A.b t.1 t.2+A.b t.1 t.2 < k) (hkU : k ≤ cellWidth A t) :
    scalarExact A R alpha t k/physicalMass A R alpha ≤ (2*K:ℝ)/A.b t.1 t.2 := by
  let N := k-10*A.d*A.b t.1 t.2
  have hb : 0 < A.b t.1 t.2 := by have h := (A.hlarge _ _ (A.hTG ht)).2; omega
  have hend := lower_tree_endpoint A R alpha t ht Y hY hr hc hy
  have hkN : k-N=10*A.d*A.b t.1 t.2 := by dsimp only [N]; omega
  have hh := scalar_exact_backward_point_bound A R alpha t ha hW B K k N (A.b t.1 t.2) hB hBK hK
    (by dsimp only [N]; omega) hb (by dsimp only [N]; omega) (by dsimp only [N]; omega)
    hkU (by rw [hkN]; exact hend)
  rwa [scalar_sum_eq_physicalMass] at hh

end ContingencyTables.RootedTreeMarginal

end OAI
