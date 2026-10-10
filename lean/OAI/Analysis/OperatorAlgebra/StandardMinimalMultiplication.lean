import OAI.Analysis.ModularTheory.StandardTensorBound
import OAI.Analysis.OperatorAlgebra.StandardCommutantOpposite
import OAI.Analysis.OperatorAlgebra.HilbertTensorExtension
import OAI.Analysis.Nuclearity.SubalgebraTensorNorm

namespace OAI

/-! The standard left/right multiplication representation extends to the
minimal tensor product for a represented quotient of a nuclear algebra. -/
noncomputable section
open MeasureTheory Filter
open scoped TensorProduct ComplexOrder
namespace WeakPureInfiniteness
open BoundedRecovery KirchbergRordam.GenericRW.GroupedFactors

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def standardRightHom (S : StandardModularData H) :
    S.M.toStarSubalgebraᵐᵒᵖ →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  S.M.commutant.toStarSubalgebra.subtype.comp (standardCommutantHom S)

lemma standardRightHom_apply (S : StandardModularData H) (b : S.M.toStarSubalgebraᵐᵒᵖ) :
    standardRightHom S b = antiunitaryConjugate S.J (star b.unop.val) := rfl

lemma standardLeftRight_commute (S : StandardModularData H)
    (a : S.M.toStarSubalgebra) (b : S.M.toStarSubalgebraᵐᵒᵖ) :
    Commute a.val (standardRightHom S b) :=
  VonNeumannAlgebra.mem_commutant_iff.mp (standardCommutantHom S b).property a.val a.property

def standardAlgebraicMultiplication (S : StandardModularData H) :
    S.M.toStarSubalgebra ⊗[ℂ] S.M.toStarSubalgebraᵐᵒᵖ →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  Pureness.commutingStarTensorHom S.M.toStarSubalgebra.subtype
    (standardRightHom S) (standardLeftRight_commute S)

lemma standardAlgebraicMultiplication_tmul (S : StandardModularData H)
    (a : S.M.toStarSubalgebra) (b : S.M.toStarSubalgebraᵐᵒᵖ) :
    standardAlgebraicMultiplication S (a ⊗ₜ[ℂ] b) =
      a.val * antiunitaryConjugate S.J (star b.unop.val) := rfl

attribute [local irreducible] standardAlgebraicMultiplication

def standardAlgebraicLinear (S : StandardModularData H) :
    S.M.toStarSubalgebra ⊗[ℂ] S.M.toStarSubalgebraᵐᵒᵖ →ₗ[ℂ] (H →L[ℂ] H) where
  toFun z := standardAlgebraicMultiplication S z
  map_add' := map_add (standardAlgebraicMultiplication S)
  map_smul' c z := map_smul (standardAlgebraicMultiplication S) c z

lemma standardAlgebraicLinear_apply (S : StandardModularData H)
    (z : S.M.toStarSubalgebra ⊗[ℂ] S.M.toStarSubalgebraᵐᵒᵖ) :
    standardAlgebraicLinear S z = standardAlgebraicMultiplication S z := rfl

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A]

lemma nuclear_quotient_standard_finite_bound
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : StandardModularData H)
    (hS : S.M = bicommutant π.range) {I : Type*} [Fintype I]
    (a : I → S.M.toStarSubalgebra) (b : I → S.M.toStarSubalgebraᵐᵒᵖ) :
    ‖∑ i, standardAlgebraicMultiplication S (a i ⊗ₜ[ℂ] b i)‖ ≤
      ‖∑ i, minimalElementary (a i) (b i)‖ := by
  simp only [standardAlgebraicMultiplication_tmul]
  have h := nuclear_quotient_standard_tensor_sum_bound ω hω hA q hq π S hS
    a (fun i => (b i).unop)
  have he := subalgebra_minimalSum_norm_le S.M a b
  exact h.trans he

lemma nuclear_quotient_standard_algebraic_bound
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : StandardModularData H)
    (hS : S.M = bicommutant π.range)
    (z : S.M.toStarSubalgebra ⊗[ℂ] S.M.toStarSubalgebraᵐᵒᵖ) :
    ‖standardAlgebraicMultiplication S z‖ ≤ ‖minimalAlgebraicLinear z‖ :=
by
  apply algebraic_linear_norm_le (standardAlgebraicMultiplication S).toLinearMap _ z
  intro n a b
  simpa only [map_sum, AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom] using
    nuclear_quotient_standard_finite_bound ω hω hA q hq π S hS a b

lemma subalgebraAlgebraicLinear_mul (M : VonNeumannAlgebra H)
    (z w : M.toStarSubalgebra ⊗[ℂ] M.toStarSubalgebraᵐᵒᵖ) :
    minimalAlgebraicLinear (z * w) = minimalAlgebraicLinear z * minimalAlgebraicLinear w := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    induction w using TensorProduct.inductionOn with
    | tmul c d =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, minimalAlgebraicLinear_tmul,
        minimalElementary_mul]
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]

lemma subalgebraAlgebraicLinear_star (M : VonNeumannAlgebra H)
    (z : M.toStarSubalgebra ⊗[ℂ] M.toStarSubalgebraᵐᵒᵖ) :
    minimalAlgebraicLinear (star z) = star (minimalAlgebraicLinear z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [TensorProduct.star_tmul, minimalAlgebraicLinear_tmul, minimalElementary_star]
  | add x y hx hy => simp only [star_add, map_add, hx, hy]

@[irreducible] def nuclearQuotientStandardMultiplication
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : StandardModularData H)
    (hS : S.M = bicommutant π.range) :
    MinimalTensor S.M.toStarSubalgebra S.M.toStarSubalgebraᵐᵒᵖ →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  denseLinearStarCompletion minimalAlgebraicLinear (standardAlgebraicLinear S)
    minimalAlgebraicLinear_dense (subalgebraAlgebraicLinear_mul S.M)
    (map_mul (standardAlgebraicMultiplication S)) (subalgebraAlgebraicLinear_star S.M)
    (map_star (standardAlgebraicMultiplication S))
    (nuclear_quotient_standard_algebraic_bound ω hω hA q hq π S hS)

end WeakPureInfiniteness

end

end OAI
