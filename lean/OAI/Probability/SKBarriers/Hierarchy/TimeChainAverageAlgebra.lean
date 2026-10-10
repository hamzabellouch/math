import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarSplit
import OAI.Probability.SKBarriers.Parisi.CDFPartitionRepresentation

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem scalarTimeChain_pairs_ofFn (n : ℕ) (β : ℝ) (p : Fin n → ℝ × ℝ≥0) (f : ℝ → ℝ) :
    scalarTimeChain β (List.ofFn p) f=
      scalarHierarchy n (fun i => (p i).1) (fun i => β*Real.sqrt ((p i).2:ℝ)) f :=
  scalarTimeChain_ofFn β n (fun i => (p i).1) (fun i => (p i).2) f

theorem scalarTimeChainAverage_append (β : ℝ) (l r : List (ℝ × ℝ≥0)) (f g : ℝ → ℝ) :
    scalarTimeChainAverage β (l++r) f g=
      scalarTimeChainAverage β l (scalarTimeChain β r f) (scalarTimeChainAverage β r f g) := by
  conv_lhs => rw [← List.ofFn_get l,← List.ofFn_get r,← List.ofFn_fin_append]
  rw [scalarTimeChainAverage_ofFn,scalarHierarchyAverage_split]
  simp only [Fin.append_left,Fin.append_right]
  conv_rhs => rw [← List.ofFn_get l,← List.ofFn_get r]
  rw [scalarTimeChain_pairs_ofFn,scalarTimeChainAverage_ofFn,scalarTimeChainAverage_ofFn]

@[simp] theorem scalarStepAverage_zero_coefficient (m : ℝ) (f g : ℝ → ℝ) :
    scalarStepAverage m 0 f g=g := by
  funext x
  simp only [scalarStepAverage,gaussianAverage,gaussianStepLaw,zero_mul,add_zero]
  rw [tilted_const,integral_const]
  simp

@[simp] theorem scalarTimeChainAverage_singleton_zero (β m : ℝ) (f g : ℝ → ℝ) :
    scalarTimeChainAverage β [(m,0)] f g=g := by
  change scalarHierarchyAverage 1 (fun _ => m) (fun _ => β*Real.sqrt (0:ℝ)) f g=g
  simp only [Real.sqrt_zero,mul_zero,scalarHierarchyAverage,scalarStepAverage_zero_coefficient]

@[simp] theorem scalarTimeChainAverage_cons_zero (β m : ℝ) (l : List (ℝ × ℝ≥0)) (f g : ℝ → ℝ) :
    scalarTimeChainAverage β ((m,0)::l) f g=scalarTimeChainAverage β l f g := by
  change scalarTimeChainAverage β ([(m,0)]++l) f g=_
  rw [scalarTimeChainAverage_append,scalarTimeChainAverage_singleton_zero]

@[simp] theorem scalarTimeChain_snoc_zero (β m : ℝ) (l : List (ℝ × ℝ≥0)) (f : ℝ → ℝ) :
    scalarTimeChain β (l++[(m,0)]) f=scalarTimeChain β l f := by
  rw [scalarTimeChain_append]
  simp [scalarTimeChain]

@[simp] theorem scalarTimeChainAverage_snoc_zero (β m : ℝ) (l : List (ℝ × ℝ≥0)) (f g : ℝ → ℝ) :
    scalarTimeChainAverage β (l++[(m,0)]) f g=scalarTimeChainAverage β l f g := by
  rw [scalarTimeChainAverage_append,scalarTimeChainAverage_singleton_zero]
  simp [scalarTimeChain]

end SK.Analytic

end
end

end OAI
