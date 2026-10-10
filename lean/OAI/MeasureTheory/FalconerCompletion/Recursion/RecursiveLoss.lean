import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Graphs.SuffixDescendants
import OAI.MeasureTheory.FalconerCompletion.Recursion.RecursiveEnvironment
import OAI.MeasureTheory.FalconerCompletion.Recursion.RecursiveUnit

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical
variable {n : ℕ}

noncomputable def recursiveLoss (n : ℕ) (C : ℝ) : ℝ := |C|+100*(n+2:ℝ)
lemma recursiveLoss_pos (n : ℕ) (C : ℝ) : 0<recursiveLoss n C := by
  unfold recursiveLoss
  positivity
lemma recursiveLoss_graph (n : ℕ) (C : ℝ) : C+36*(n+1:ℝ)+5≤2*recursiveLoss n C := by
  unfold recursiveLoss
  nlinarith [le_abs_self C,abs_nonneg C,(Nat.cast_nonneg n : (0:ℝ)≤(n:ℝ))]
lemma recursiveLoss_dim (n : ℕ) (C : ℝ) : 4*(n+2:ℝ)≤2*recursiveLoss n C := by
  unfold recursiveLoss
  nlinarith [abs_nonneg C,(Nat.cast_nonneg n : (0:ℝ)≤(n:ℝ))]
lemma recursiveLoss_test (n : ℕ) (C : ℝ) : C≤2*recursiveLoss n C := by
  unfold recursiveLoss
  nlinarith [le_abs_self C,abs_nonneg C,(Nat.cast_nonneg n : (0:ℝ)≤(n:ℝ))]

lemma weighted_child_cap {N : ℕ} {a b x M : ℝ} (hx : 0≤x) (hab : a≤b)
    (h : ((2:ℝ)^N)^b*x≤M) : ((2:ℝ)^N)^a*x≤M :=
  (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le
    (one_le_pow₀ (by norm_num)) hab) hx).trans h

lemma farSeparated_centre {a : ℕ} {K : ℝ} {X Y : CellPath (n+1)}
    (hX : X.length=a) (hY : Y.length=a)
    (h : Attempt4FullFar.farSeparatedGridND a K (fun j => (pathIndex X j:ℤ)) (fun j => (pathIndex Y j:ℤ))) :
    CentreSeparated X Y a K := by
  unfold CentreSeparated treeCenter
  rw [hX,hY]
  change K/8/(2:ℝ)^a≤_ ∧ _≤_
  simpa only [Attempt4FullFar.farSeparatedGridND,div_div,ambientGridCenter,Attempt4FullFar.ambientGridCenter] using h

lemma RecursiveEnvironmentND.distance_mem (e : RecursiveEnvironmentND n) (K : ℝ)
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (total : ℕ) (Ψ : ℝ → ℝ) (a t i : ℕ) (X Y : CellPath (n+1))
    (hX : X∈dyadicPaths a) (hY : Y∈dyadicPaths a)
    (hox : 0<e.ρ (treeCell X)) (hoy : 0<e.ρ (treeCell Y))
    (hsep : Attempt4FullFar.farSeparatedGridND a K (fun j => (pathIndex X j:ℤ)) (fun j => (pathIndex Y j:ℤ))) :
    e.energies K W total Ψ (.D a t i) ((e.distanceData a t i X Y).coincidence.toReal) :=
  ⟨X,Y,hX,hY,hox,hoy,hsep,rfl⟩

end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
