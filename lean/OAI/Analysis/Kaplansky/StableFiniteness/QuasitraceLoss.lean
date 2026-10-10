import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Regular.ReducedTensor
import OAI.Analysis.Kaplansky.StableFiniteness.FaithfulRepresentation

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped ComplexOrder BigOperators
open Kaplansky Regular
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2100] closedSubalgebraLE closedSubalgebraPreorder

lemma actualAlgebra_tensor_properlyInfinite :
    ProperlyInfinite (tensorAlgebra (G:=F2) actualFaithfulRepresentation) := by
  have tensorInfinite {AlgebraType HilbertType : Type} [CStarAlgebra AlgebraType]
      [NormedAddCommGroup HilbertType] [InnerProductSpace ℂ HilbertType]
      [CompleteSpace HilbertType]
      (representation : AlgebraType →⋆ₐ[ℂ] (HilbertType →L[ℂ] HilbertType))
      (tuple : Fin 24 → AlgebraType)
      (columnSum : ∑ index, star (tuple index) * tuple index = 1)
      (rowBound : ∑ index, tuple index * star (tuple index) ≤
        (2/3:ℂ) • (1:AlgebraType)) :
      ProperlyInfinite (tensorAlgebra (G:=F2) representation) := by
    apply tensor_two_isometries_of_row_contraction representation tuple (2/3)
      (by norm_num) (by norm_num) columnSum
    have scalar_eq : (2/3:ℝ) • (1:AlgebraType) = (2/3:ℂ) • (1:AlgebraType) := by
      rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) (2/3:ℝ) (1:AlgebraType)]
      exact congrArg (fun scalar : ℂ => scalar • (1:AlgebraType)) (by norm_num)
    rwa [scalar_eq]
  exact tensorInfinite actualFaithfulRepresentation
    (generatedGenerator actualBoundedGenerator) actual_test_shift_algebra.2.2.1
    actual_test_shift_algebra.2.2.2

theorem reduced_quasitrace_loss_exists : ReducedQuasitraceLoss := by
  let d : CuntzDimensionState ActualAlgebra := Classical.choice
    (cuntzDimensionState_nonempty fun k hk => actualAlgebra_matrix_not_properlyInfinite hk)
  refine ⟨ActualAlgebra,inferInstance,actualAlgebra_nontrivial_separable.1,
    actualAlgebra_nontrivial_separable.2,?_,ActualRepresentationHilbert,inferInstance,inferInstance,
    inferInstance,actualFaithfulRepresentation,actualFaithfulRepresentation_injective,
    actualAlgebra_tensor_properlyInfinite,?_⟩
  · exact d.normalizedTwoQuasitrace_exists
  · rintro ⟨τ,hτ,_⟩
    exact not_properlyInfinite τ hτ actualAlgebra_tensor_properlyInfinite


end KaplanskyConsequences

end

end OAI
