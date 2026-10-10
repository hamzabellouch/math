import Mathlib
import OAI.Probability.SKBarriers.Scalar.VectorAverage

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorHierarchy_cast {n r : ℕ} (h : n=r) (m : Fin n → ℝ)
    (v : Fin n → E) (f : E → ℝ) :
    vectorHierarchy n m v f=vectorHierarchy r (fun i => m (Fin.cast h.symm i))
      (fun i => v (Fin.cast h.symm i)) f := by
  subst r; rfl

theorem vectorHierarchyAverage_cast {n r : ℕ} (h : n=r) (m : Fin n → ℝ)
    (v : Fin n → E) (f g : E → ℝ) :
    vectorHierarchyAverage n m v f g=vectorHierarchyAverage r (fun i => m (Fin.cast h.symm i))
      (fun i => v (Fin.cast h.symm i)) f g := by
  subst r; rfl

def vectorBlockHierarchy (r : ℕ) : (n : ℕ) → (Fin n → ℝ) → (Fin n → Fin r → E) → (E → ℝ) → E → ℝ
  | 0,_,_,f => f
  | n+1,m,v,f => vectorBlockHierarchy r n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorHierarchy r (fun _ => m (Fin.last n)) (v (Fin.last n)) f)

def vectorBlockHierarchyAverage (r : ℕ) : (n : ℕ) → (Fin n → ℝ) → (Fin n → Fin r → E) →
    (E → ℝ) → (E → ℝ) → E → ℝ
  | 0,_,_,_,g => g
  | n+1,m,v,f,g => vectorBlockHierarchyAverage r n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorHierarchy r (fun _ => m (Fin.last n)) (v (Fin.last n)) f)
      (vectorHierarchyAverage r (fun _ => m (Fin.last n)) (v (Fin.last n)) f g)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem finProd_symm_prefix (n r : ℕ) (i : Fin (n*r)) :
    finProdFinEquiv.symm (Fin.cast (Nat.succ_mul n r).symm (i.castAdd r))=
      ((finProdFinEquiv.symm i).1.castSucc,(finProdFinEquiv.symm i).2) := by
  apply Prod.ext <;> apply Fin.ext <;> rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem finProd_symm_suffix (n r : ℕ) (i : Fin r) :
    finProdFinEquiv.symm (Fin.cast (Nat.succ_mul n r).symm (i.natAdd (n*r)))=(Fin.last n,i) := by
  apply finProdFinEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  change n*r+i.val=i.val+r*n
  ring

theorem vectorHierarchy_blocks (n r : ℕ) (m : Fin n → ℝ) (v : Fin n → Fin r → E) (f : E → ℝ) :
    vectorHierarchy (n*r) (fun i => m (finProdFinEquiv.symm i).1)
      (fun i => v (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) f=
      vectorBlockHierarchy r n m v f := by
  induction n generalizing f with
  | zero => rw [vectorHierarchy_cast (Nat.zero_mul r)]; rfl
  | succ n ih =>
    rw [vectorHierarchy_cast (Nat.succ_mul n r),vectorHierarchy_split]
    simp only [finProd_symm_prefix,finProd_symm_suffix]
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc) _

theorem vectorHierarchyAverage_blocks (n r : ℕ) (m : Fin n → ℝ) (v : Fin n → Fin r → E)
    (f g : E → ℝ) :
    vectorHierarchyAverage (n*r) (fun i => m (finProdFinEquiv.symm i).1)
      (fun i => v (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) f g=
      vectorBlockHierarchyAverage r n m v f g := by
  induction n generalizing f g with
  | zero => rw [vectorHierarchyAverage_cast (Nat.zero_mul r)]; rfl
  | succ n ih =>
    rw [vectorHierarchyAverage_cast (Nat.succ_mul n r),vectorHierarchyAverage_split]
    simp only [finProd_symm_prefix,finProd_symm_suffix]
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc) _ _
end

end SK.Analytic

end
end

end OAI
