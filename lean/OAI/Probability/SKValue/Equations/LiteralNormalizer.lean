import Mathlib
import OAI.Probability.SKValue.Processes.MeshRaw

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue

end SKValue

namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma literal_normalizer (W : BrownianSpace) (γ : OrderParameter) (T : ℝ) (N j : ℕ) :
    normalizer W γ T N j =
      predictableNormalizer (meshRaw T N γ.coeff (gradient W γ) j) (gaussianProduct (Fin (N+1))) := rfl

lemma literal_coefficientA_succ (W : BrownianSpace) (γ : OrderParameter) (T : ℝ) (N j : ℕ) :
    coefficientA W γ T N (j+1)=meshA T N γ.coeff (gradient W γ) j := by
  simp only [coefficientA, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
  rfl

lemma literal_coefficientB_succ (W : BrownianSpace) (γ : OrderParameter) (T : ℝ) (N j : ℕ) :
    coefficientB W γ T N (j+1)=meshB T N γ.coeff (gradient W γ) j := by
  simp only [coefficientB, Nat.add_sub_cancel]
  rfl

lemma literal_shiftedCoefficientSum (W : BrownianSpace) (γ : OrderParameter) (T : ℝ) (N : ℕ) :
    shiftedCoefficientSum W γ T N=finiteShiftedValue T N γ.coeff (gradient W γ) := by
  unfold shiftedCoefficientSum
  rw [←Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ]
  simp only [Fin.val_zero, coefficientA, ↓reduceIte, zero_mul, zero_add]
  unfold finiteShiftedValue
  apply Finset.sum_congr rfl
  intro i hi
  change coefficientA W γ T N ((i : ℕ)+1)*coefficientB W γ T N (((i : ℕ)+1)+1)=_
  rw [literal_coefficientA_succ, literal_coefficientB_succ]

end SKValue

end

end OAI
