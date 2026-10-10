import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarSplit
import OAI.Probability.SKBarriers.Replicas.PairRecursion

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def pairIndependentHierarchy : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) →
    (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | 0,_,_,f => f
  | n+1,m,v,f => pairIndependentHierarchy n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (pairIndependentStep (m (Fin.last n)) (v (Fin.last n)) f)

def pairIndependentHierarchyAverage : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) →
    (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | 0,_,_,_,g => g
  | n+1,m,v,f,g => pairIndependentHierarchyAverage n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (pairIndependentStep (m (Fin.last n)) (v (Fin.last n)) f)
      (pairIndependentAverage (m (Fin.last n)) (v (Fin.last n)) f g)

theorem pairIndependentHierarchy_separate (n : ℕ) (m v : Fin n → ℝ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g) :
    pairIndependentHierarchy n m v (fun p => f p.1+g p.2)=
      fun p => scalarHierarchy n m v f p.1+scalarHierarchy n m v g p.2 := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [pairIndependentHierarchy,pairIndependentStep_separate hf hg,ih _ _
      (scalarStep_regular hf _ _) (scalarStep_regular hg _ _)]
    rfl

theorem pairIndependentHierarchyAverage_product (n : ℕ) (m v : Fin n → ℝ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g) (a b : ℝ → ℝ) :
    pairIndependentHierarchyAverage n m v (fun p => f p.1+g p.2) (fun p => a p.1*b p.2)=
      fun p => scalarHierarchyAverage n m v f a p.1*scalarHierarchyAverage n m v g b p.2 := by
  induction n generalizing f g a b with
  | zero => rfl
  | succ n ih =>
    rw [pairIndependentHierarchyAverage,pairIndependentStep_separate hf hg,
      pairIndependentAverage_product hg,ih _ _ (scalarStep_regular hf _ _) (scalarStep_regular hg _ _)]
    rfl

def pairCommonHierarchy : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) →
    (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | 0,_,_,f => f
  | n+1,m,v,f => pairCommonHierarchy n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorStep (m (Fin.last n)/2) (v (Fin.last n),v (Fin.last n)) f)

def pairCommonHierarchyAverage : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) →
    (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ) → ℝ × ℝ → ℝ
  | 0,_,_,_,g => g
  | n+1,m,v,f,g => pairCommonHierarchyAverage n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorStep (m (Fin.last n)/2) (v (Fin.last n),v (Fin.last n)) f)
      (vectorStepAverage (m (Fin.last n)/2) (v (Fin.last n),v (Fin.last n)) f g)

theorem pairCommonHierarchy_diagonal (n : ℕ) (m v : Fin n → ℝ)
    (F : ℝ × ℝ → ℝ) (f : ℝ → ℝ) (h : ∀ x, F (x,x)=2*f x) (x : ℝ) :
    pairCommonHierarchy n m v F (x,x)=2*scalarHierarchy n m v f x := by
  induction n generalizing f F with
  | zero => exact h x
  | succ n ih =>
    exact ih _ _ _ _ (vectorStep_pair_diagonal F f h _ _)

theorem pairCommonHierarchyAverage_diagonal (n : ℕ) (m v : Fin n → ℝ)
    (F G : ℝ × ℝ → ℝ) (f g : ℝ → ℝ) (h : ∀ x, F (x,x)=2*f x)
    (hg : ∀ x, G (x,x)=g x) (x : ℝ) :
    pairCommonHierarchyAverage n m v F G (x,x)=scalarHierarchyAverage n m v f g x := by
  induction n generalizing f g F G with
  | zero => exact hg x
  | succ n ih =>
    exact ih _ _ _ _ _ _ (vectorStep_pair_diagonal F f h _ _)
      (vectorStepAverage_pair_diagonal F G f g h hg _ _)

theorem pairSplit_pressure (a b : ℕ) (m v : Fin (a+b) → ℝ)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (x : ℝ) :
    pairCommonHierarchy a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
      (pairIndependentHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a))
        (fun p => f p.1+f p.2)) (x,x)=2*scalarHierarchy (a+b) m v f x := by
  rw [pairIndependentHierarchy_separate b _ _ hf hf,scalarHierarchy_split a b]
  exact pairCommonHierarchy_diagonal a _ _ _ _ (fun y => by ring) x

theorem pairSplit_overlap (a b : ℕ) (m v : Fin (a+b) → ℝ)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (g : ℝ → ℝ) (x : ℝ) :
    pairCommonHierarchyAverage a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
      (pairIndependentHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a))
        (fun p => f p.1+f p.2))
      (pairIndependentHierarchyAverage b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a))
        (fun p => f p.1+f p.2) (fun p => g p.1*g p.2)) (x,x)=
      scalarMomentSquare (a+b) m v f g ⟨a,by omega⟩ x := by
  rw [pairIndependentHierarchy_separate b _ _ hf hf,pairIndependentHierarchyAverage_product b _ _ hf hf,
    scalarMomentSquare_split a b]
  exact pairCommonHierarchyAverage_diagonal a _ _ _ _ _ _ (fun y => by ring)
    (fun y => (pow_two _).symm) x

end SK.Analytic

end
end

end OAI
