import Mathlib
import OAI.Analysis.WeakInfiniteness.RectangularPolar

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

local instance matrixRealModuleFour {j : Type*} [Fintype j] :
    Module ℝ (CStarMatrix j j A) := Module.complexToReal _

lemma norm_rectangular_sqrt_left (U : CStarMatrix m n A) (V : CStarMatrix n k A) :
    ‖CFC.sqrt (U.conjTranspose*U)*V‖=‖U*V‖ := by
  have he : (CFC.sqrt (U.conjTranspose*U)*V).conjTranspose*
      (CFC.sqrt (U.conjTranspose*U)*V)=(U*V).conjTranspose*(U*V) := by
    rw [rectangular_star_mul,rectangular_star_mul]
    change (V.conjTranspose*star (CFC.sqrt (U.conjTranspose*U)))*
      (CFC.sqrt (U.conjTranspose*U)*V)=(V.conjTranspose*U.conjTranspose)*(U*V)
    rw [(CFC.sqrt_nonneg (U.conjTranspose*U)).star_eq]
    calc
      _=V.conjTranspose*(CFC.sqrt (U.conjTranspose*U)*CFC.sqrt (U.conjTranspose*U))*V := by
        simp only [rectangular_mul_assoc]
      _=V.conjTranspose*(U.conjTranspose*U)*V := by
        rw [CFC.sqrt_mul_sqrt_self _ (rectangular_initial_nonneg U)]
      _=_ := by simp only [rectangular_mul_assoc]
  have hn := congrArg norm he
  rw [rectangular_norm_initial,rectangular_norm_initial] at hn
  nlinarith [norm_nonneg (CFC.sqrt (U.conjTranspose*U)*V),norm_nonneg (U*V)]

lemma norm_rectangular_sqrt_right (U : CStarMatrix m n A) (V : CStarMatrix k n A) :
    ‖U*CFC.sqrt (V.conjTranspose*V)‖=‖U*V.conjTranspose‖ := by
  have h := norm_rectangular_sqrt_left V U.conjTranspose
  have h1 : (U*CFC.sqrt (V.conjTranspose*V)).conjTranspose=
      CFC.sqrt (V.conjTranspose*V)*U.conjTranspose := by
    rw [rectangular_star_mul]
    change star (CFC.sqrt (V.conjTranspose*V))*U.conjTranspose=_
    rw [(CFC.sqrt_nonneg (V.conjTranspose*V)).star_eq]
  have h2 : (U*V.conjTranspose).conjTranspose=V*U.conjTranspose := by
    rw [rectangular_star_mul,rectangular_conjTranspose_conjTranspose]
  rw [← h1,← h2,rectangular_norm_conjTranspose,rectangular_norm_conjTranspose] at h
  exact h

lemma norm_rectangular_range_roots (U : CStarMatrix m n A) (V : CStarMatrix m k A) :
    ‖CFC.sqrt (U*U.conjTranspose)*CFC.sqrt (V*V.conjTranspose)‖=
      ‖U.conjTranspose*V‖ := by
  have h1 := norm_rectangular_sqrt_left U.conjTranspose (CFC.sqrt (V*V.conjTranspose))
  have h2 := norm_rectangular_sqrt_right U.conjTranspose V.conjTranspose
  simp only [rectangular_conjTranspose_conjTranspose] at h1 h2
  exact h1.trans h2

open WithCStarModule in
lemma norm_matrix_le_sum_entries (M : CStarMatrix m n A) : ‖M‖ ≤ ∑ j,∑ i,‖M i j‖ := by
  rw [CStarMatrix.norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simp only [CStarMatrix.toCLM_apply_eq_sum,Finset.sum_mul]
  apply (pi_norm_le_sum_norm _).trans
  gcongr with i _
  apply (norm_sum_le _ _).trans
  gcongr with j _
  apply (norm_mul_le _ _).trans
  rw [mul_comm]
  gcongr
  exact WithCStarModule.norm_apply_le_norm v j

end

end

end WeakPureInfiniteness
end

end OAI
