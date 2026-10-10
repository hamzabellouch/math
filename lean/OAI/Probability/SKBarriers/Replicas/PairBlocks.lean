import Mathlib
import OAI.Probability.SKBarriers.Scalar.VectorBlocks
import OAI.Probability.SKBarriers.Replicas.PairSplit

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

@[simp] theorem vectorStepAverage_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℝ) (f g : E → ℝ) : vectorStepAverage m 0 f g=g := by
  funext x
  simp only [vectorStepAverage,smul_zero,add_zero,gaussianAverage,gaussianStepLaw,tilted_const]
  simp

def pairBlockVector (shared : Bool) (v : ℝ) (u : Fin 2) : ℝ × ℝ :=
  if shared then if u=0 then (v,v) else 0 else if u=0 then (v,0) else (0,v)

theorem vectorHierarchy_pairBlock (shared : Bool) (m v : ℝ) (f : ℝ × ℝ → ℝ) :
    vectorHierarchy 2 (fun _ => m) (pairBlockVector shared v) f=
      if shared then vectorStep m (v,v) f else pairIndependentStep m v f := by
  cases shared <;> simp [vectorHierarchy,pairBlockVector,pairIndependentStep]

theorem vectorHierarchyAverage_pairBlock (shared : Bool) (m v : ℝ) (f g : ℝ × ℝ → ℝ) :
    vectorHierarchyAverage 2 (fun _ => m) (pairBlockVector shared v) f g=
      if shared then vectorStepAverage m (v,v) f g else pairIndependentAverage m v f g := by
  cases shared <;> simp [vectorHierarchyAverage,pairBlockVector,pairIndependentAverage]

section Blocks
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorBlockHierarchy_split (a b r : ℕ) (m : Fin (a+b) → ℝ)
    (v : Fin (a+b) → Fin r → E) (f : E → ℝ) :
    vectorBlockHierarchy r (a+b) m v f=
      vectorBlockHierarchy r a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (vectorBlockHierarchy r b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f) := by
  induction b generalizing f with
  | zero => rfl
  | succ b ih =>
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorHierarchy r (fun _ => m (Fin.last (a+b))) (v (Fin.last (a+b))) f)

theorem vectorBlockHierarchyAverage_split (a b r : ℕ) (m : Fin (a+b) → ℝ)
    (v : Fin (a+b) → Fin r → E) (f g : E → ℝ) :
    vectorBlockHierarchyAverage r (a+b) m v f g=
      vectorBlockHierarchyAverage r a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (vectorBlockHierarchy r b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f)
        (vectorBlockHierarchyAverage r b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f g) := by
  induction b generalizing f g with
  | zero => rfl
  | succ b ih =>
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorHierarchy r (fun _ => m (Fin.last (a+b))) (v (Fin.last (a+b))) f)
      (vectorHierarchyAverage r (fun _ => m (Fin.last (a+b))) (v (Fin.last (a+b))) f g)
end Blocks

theorem vectorBlockHierarchy_independent (n : ℕ) (m v : Fin n → ℝ) (f : ℝ × ℝ → ℝ) :
    vectorBlockHierarchy 2 n m (fun i => pairBlockVector false (v i)) f=pairIndependentHierarchy n m v f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [vectorBlockHierarchy,vectorHierarchy_pairBlock]
    exact ih _ _ _

theorem vectorBlockHierarchy_common (n : ℕ) (m v : Fin n → ℝ) (f : ℝ × ℝ → ℝ) :
    vectorBlockHierarchy 2 n (fun i => m i/2) (fun i => pairBlockVector true (v i)) f=pairCommonHierarchy n m v f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [vectorBlockHierarchy,vectorHierarchy_pairBlock]
    exact ih _ _ _

theorem vectorBlockHierarchyAverage_independent (n : ℕ) (m v : Fin n → ℝ) (f g : ℝ × ℝ → ℝ) :
    vectorBlockHierarchyAverage 2 n m (fun i => pairBlockVector false (v i)) f g=pairIndependentHierarchyAverage n m v f g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [vectorBlockHierarchyAverage,vectorHierarchy_pairBlock,vectorHierarchyAverage_pairBlock]
    exact ih _ _ _ _

theorem vectorBlockHierarchyAverage_common (n : ℕ) (m v : Fin n → ℝ) (f g : ℝ × ℝ → ℝ) :
    vectorBlockHierarchyAverage 2 n (fun i => m i/2) (fun i => pairBlockVector true (v i)) f g=pairCommonHierarchyAverage n m v f g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [vectorBlockHierarchyAverage,vectorHierarchy_pairBlock,vectorHierarchyAverage_pairBlock]
    exact ih _ _ _ _

def splitPairMass {n : ℕ} (a : ℕ) (m : Fin n → ℝ) (j : Fin n) : ℝ := if j.val<a then m j/2 else m j

def splitPairVector {n : ℕ} (a : ℕ) (v : Fin n → ℝ) (j : Fin n) : Fin 2 → ℝ × ℝ :=
  pairBlockVector (decide (j.val<a)) (v j)

theorem splitPairVector_prefix (a b : ℕ) (v : Fin (a+b) → ℝ) (i : Fin a) :
    splitPairVector a v (i.castAdd b)=pairBlockVector true (v (i.castAdd b)) := by
  simp [splitPairVector,i.isLt]

theorem splitPairVector_suffix (a b : ℕ) (v : Fin (a+b) → ℝ) (i : Fin b) :
    splitPairVector a v (i.natAdd a)=pairBlockVector false (v (i.natAdd a)) := by
  simp [splitPairVector]

theorem splitPairMass_prefix (a b : ℕ) (m : Fin (a+b) → ℝ) (i : Fin a) :
    splitPairMass a m (i.castAdd b)=m (i.castAdd b)/2 := by simp [splitPairMass,i.isLt]

theorem splitPairMass_suffix (a b : ℕ) (m : Fin (a+b) → ℝ) (i : Fin b) :
    splitPairMass a m (i.natAdd a)=m (i.natAdd a) := by simp [splitPairMass]

theorem splitPairHierarchy (a b : ℕ) (m v : Fin (a+b) → ℝ) (f : ℝ × ℝ → ℝ) :
    vectorBlockHierarchy 2 (a+b) (splitPairMass a m) (splitPairVector a v) f=
      pairCommonHierarchy a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (pairIndependentHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f) := by
  rw [vectorBlockHierarchy_split a b]
  simp only [splitPairVector_prefix,splitPairVector_suffix,splitPairMass_prefix,splitPairMass_suffix]
  rw [vectorBlockHierarchy_independent,vectorBlockHierarchy_common]

theorem splitPairHierarchyAverage (a b : ℕ) (m v : Fin (a+b) → ℝ) (f g : ℝ × ℝ → ℝ) :
    vectorBlockHierarchyAverage 2 (a+b) (splitPairMass a m) (splitPairVector a v) f g=
      pairCommonHierarchyAverage a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (pairIndependentHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f)
        (pairIndependentHierarchyAverage b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f g) := by
  rw [vectorBlockHierarchyAverage_split a b]
  simp only [splitPairVector_prefix,splitPairVector_suffix,splitPairMass_prefix,splitPairMass_suffix]
  rw [vectorBlockHierarchy_independent,vectorBlockHierarchyAverage_independent,vectorBlockHierarchyAverage_common]

end SK.Analytic

end
end

end OAI
