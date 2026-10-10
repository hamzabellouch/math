import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open FourierTransform TemperedDistribution MeasureTheory
open scoped SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open MeasureTheory
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def basisWordEval (b : Module.Basis ι ℝ E) (n : ℕ) :
    (E [×n]→L[ℝ] ℂ) →ₗ[ℝ] ((Fin n → ι) → ℂ) where
  toFun T w := T (fun i => b (w i))
  map_add' T U := by ext w; rfl
  map_smul' c T := by ext w; rfl

omit [Fintype ι] in
lemma basisWordEval_injective (b : Module.Basis ι ℝ E) (n : ℕ) :
    Function.Injective (basisWordEval b n) := by
  intro T U h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ => b)
  intro w
  exact congrFun h w

theorem multilinear_norm_le_basis_sum (b : Module.Basis ι ℝ E) (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ T : E [×n]→L[ℝ] ℂ,
      ‖T‖ ≤ C * ∑ w : Fin n → ι,
        ‖T (fun i => b (w i))‖ := by
  classical
  let : FiniteDimensional ℝ (E [×n]→L[ℝ] ℂ) :=
    FiniteDimensional.of_injective (basisWordEval b n) (basisWordEval_injective b n)
  obtain ⟨K, hK, ha⟩ := (basisWordEval b n).injective_iff_antilipschitz.mp
    (basisWordEval_injective b n)
  refine ⟨K, hK, fun T => ?_⟩
  refine (ZeroHomClass.bound_of_antilipschitz (basisWordEval b n) ha T).trans ?_
  apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).2
  intro w
  exact Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ w)

end YauCounterexamples

open MeasureTheory Set
open scoped ENNReal NNReal

end

end OAI
