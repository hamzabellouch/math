import Mathlib
import OAI.Probability.SKBarriers.Replicas.PairRecursion

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

abbrev BranchIncrement := ℝ × ℝ
abbrev TaggedBranchIncrement := Sum BranchIncrement BranchIncrement

def branchMass : TaggedBranchIncrement → ℝ
  | .inl p => p.1
  | .inr p => p.1/2

def branchVector : TaggedBranchIncrement → ℝ × ℝ
  | .inl p => (p.2,0)
  | .inr p => (0,p.2)

def scalarIncrementChain : List BranchIncrement → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | p::l, f => scalarStep p.1 p.2 (scalarIncrementChain l f)

def scalarIncrementAverage : List BranchIncrement → (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | [], _, g => g
  | p::l, f, g => scalarStepAverage p.1 p.2 (scalarIncrementChain l f) (scalarIncrementAverage l f g)

def taggedBranchChain : List TaggedBranchIncrement → (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | [], f => f
  | p::l, f => vectorStep (branchMass p) (branchVector p) (taggedBranchChain l f)

def taggedBranchAverage : List TaggedBranchIncrement → (ℝ × ℝ → ℝ) →
    (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | [], _, g => g
  | p::l, f, g => vectorStepAverage (branchMass p) (branchVector p)
      (taggedBranchChain l f) (taggedBranchAverage l f g)

def leftBranch (l : List TaggedBranchIncrement) : List BranchIncrement :=
  l.filterMap (fun p => match p with | .inl q => some q | .inr _ => none)
def rightBranch (l : List TaggedBranchIncrement) : List BranchIncrement :=
  l.filterMap (fun p => match p with | .inl _ => none | .inr q => some q)

theorem scalarIncrementChain_regular (l : List BranchIncrement) {f : ℝ → ℝ}
    (hf : BoundedDerivs f) : BoundedDerivs (scalarIncrementChain l f) := by
  induction l with
  | nil => exact hf
  | cons p l ih => exact scalarStep_regular ih p.1 p.2

theorem scalarStep_half_double (m v : ℝ) (f : ℝ → ℝ) :
    scalarStep (m/2) v (fun x => 2*f x)=fun x => 2*scalarStep m v f x := by
  exact gaussianStep_half_double m _

theorem scalarStepAverage_half_double (m v : ℝ) (f g : ℝ → ℝ) :
    scalarStepAverage (m/2) v (fun x => 2*f x) g=scalarStepAverage m v f g := by
  funext x
  exact congrFun (gaussianAverage_half_double m
    (fun z : ℝ × ℝ => f (z.1+v*z.2)) (fun z => g (z.1+v*z.2))) x

theorem taggedBranchChain_factor (l : List TaggedBranchIncrement) {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) :
    taggedBranchChain l (fun p => f p.1+2*g p.2)=
      fun p => scalarIncrementChain (leftBranch l) f p.1+
        2*scalarIncrementChain (rightBranch l) g p.2 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    cases p with
    | inl p =>
      rw [taggedBranchChain,ih]
      simpa only [branchMass,branchVector,leftBranch,rightBranch,List.filterMap_cons,scalarIncrementChain] using
        vectorStep_pair_left (g:=fun z => 2*scalarIncrementChain (rightBranch l) g z)
          (scalarIncrementChain_regular (leftBranch l) hf) p.1 p.2
    | inr p =>
      rw [taggedBranchChain,ih]
      change vectorStep (p.1/2) (0,p.2)
        (fun z => scalarIncrementChain (leftBranch l) f z.1+2*scalarIncrementChain (rightBranch l) g z.2)=_
      rw [vectorStep_pair_right ((scalarIncrementChain_regular _ hg).const_mul 2),scalarStep_half_double]
      rfl

theorem taggedBranchAverage_factor (l : List TaggedBranchIncrement) {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) (a b : ℝ → ℝ) :
    taggedBranchAverage l (fun p => f p.1+2*g p.2) (fun p => a p.1*b p.2)=
      fun p => scalarIncrementAverage (leftBranch l) f a p.1*
        scalarIncrementAverage (rightBranch l) g b p.2 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [taggedBranchAverage,taggedBranchChain_factor l hf hg,ih]
    cases p with
    | inl p =>
      simpa only [branchMass,branchVector,leftBranch,rightBranch,List.filterMap_cons,scalarIncrementAverage] using
        vectorStepAverage_pair_left (scalarIncrementChain (leftBranch l) f)
          (fun z => 2*scalarIncrementChain (rightBranch l) g z)
          (scalarIncrementAverage (leftBranch l) f a) (scalarIncrementAverage (rightBranch l) g b) p.1 p.2
    | inr p =>
      change vectorStepAverage (p.1/2) (0,p.2)
        (fun z => scalarIncrementChain (leftBranch l) f z.1+2*scalarIncrementChain (rightBranch l) g z.2)
        (fun z => scalarIncrementAverage (leftBranch l) f a z.1*scalarIncrementAverage (rightBranch l) g b z.2)=_
      rw [vectorStepAverage_pair_right (scalarIncrementChain (leftBranch l) f)
        (fun z => 2*scalarIncrementChain (rightBranch l) g z)
        (scalarIncrementAverage (leftBranch l) f a) (scalarIncrementAverage (rightBranch l) g b),
        scalarStepAverage_half_double]
      rfl

def mergedBranches (l r : List BranchIncrement) : List TaggedBranchIncrement :=
  (l.map Sum.inl).merge (r.map Sum.inr) (fun p q => decide (branchMass p ≤ branchMass q))

theorem mergedBranches_left (l r : List BranchIncrement) :
    leftBranch (mergedBranches l r)=l := by
  induction l generalizing r with
  | nil => simp [mergedBranches,leftBranch,List.filterMap_map]
  | cons p l ih =>
    induction r with
    | nil => simp [mergedBranches,leftBranch,List.filterMap_map]
    | cons q r ihr =>
      unfold mergedBranches
      simp only [List.map_cons,List.cons_merge_cons]
      split
      · simp only [leftBranch,List.filterMap_cons]
        exact congrArg (List.cons p) (ih (q::r))
      · simp only [leftBranch,List.filterMap_cons]
        exact ihr

theorem mergedBranches_right (l r : List BranchIncrement) :
    rightBranch (mergedBranches l r)=r := by
  induction l generalizing r with
  | nil => simp [mergedBranches,rightBranch,List.filterMap_map]
  | cons p l ih =>
    induction r with
    | nil => simp [mergedBranches,rightBranch,List.filterMap_map]
    | cons q r ihr =>
      unfold mergedBranches
      simp only [List.map_cons,List.cons_merge_cons]
      split
      · simp only [rightBranch,List.filterMap_cons]
        exact ih (q::r)
      · simp only [rightBranch,List.filterMap_cons]
        exact congrArg (List.cons q) ihr

theorem mergedBranches_monotone (l r : List BranchIncrement)
    (hl : l.Pairwise (fun p q => p.1 ≤ q.1))
    (hr : r.Pairwise (fun p q => p.1 ≤ q.1)) :
    (mergedBranches l r).Pairwise (fun p q => branchMass p ≤ branchMass q) := by
  unfold mergedBranches
  have hl' : (l.map (Sum.inl : BranchIncrement → TaggedBranchIncrement)).Pairwise
      (fun p q => branchMass p ≤ branchMass q) := by simpa [List.pairwise_map,branchMass] using hl
  have hr' : (r.map (Sum.inr : BranchIncrement → TaggedBranchIncrement)).Pairwise
      (fun p q => branchMass p ≤ branchMass q) := by
    rw [List.pairwise_map]
    exact hr.imp (fun h => div_le_div_of_nonneg_right h (by norm_num))
  have ht : ∀ a b c : TaggedBranchIncrement,
      decide (branchMass a ≤ branchMass b) = true →
      decide (branchMass b ≤ branchMass c) = true →
      decide (branchMass a ≤ branchMass c) = true := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at hab hbc ⊢
    exact le_trans hab hbc
  have htot : ∀ a b : TaggedBranchIncrement,
      (decide (branchMass a ≤ branchMass b) || decide (branchMass b ≤ branchMass a)) = true := by
    intro a b
    simp only [Bool.or_eq_true,decide_eq_true_eq]
    exact le_total _ _
  simpa only [decide_eq_true_eq] using List.pairwise_merge ht htot
    _ _ (by simpa only [decide_eq_true_eq] using hl') (by simpa only [decide_eq_true_eq] using hr')

end SK.Analytic

end
end

end OAI
