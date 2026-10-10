import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinLocalParameters
import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnitParameterInverse
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialProduct

namespace OAI

/-! # Local regularity of the intrinsic exponential from BCH

The BCH basis-input polynomial has identity derivative. Composing its local
inverse with the smooth product of one-parameter subgroups constructs local
exponential coordinates, without an assumed global logarithm.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

omit [FiniteDimensional ℝ E] [LieGroup (𝓘(ℝ, E)) ⊤ G] in
theorem exponentialProduct_eq_list_prod
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) {n : ℕ}
    (v : Fin n → E) (x : Fin n → ℝ) :
    exponentialProduct Exp v x = (List.ofFn (fun i => Exp (x i • v i))).prod := by
  induction n with
  | zero => simp [exponentialProduct]
  | succ n ih =>
    simp only [exponentialProduct, List.ofFn_succ, List.prod_cons]
    rw [ih]
    rfl

theorem exponential_comp_basisDynkinParameter
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} {c n : ℕ}
    (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G,
      (List.ofFn (fun i => Exp (X i))).prod = Exp (finiteDynkinPolynomial coeff X))
    (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    (Exp ∘ b.equivFun.symm) ∘ basisDynkinParameter coeff b =
      exponentialProduct Exp (fun i => (b i : E)) := by
  funext x
  change Exp (b.equivFun.symm (basisDynkinParameter coeff b x)) = _
  rw [basisDynkinParameter_eq, b.equivFun.symm_apply_apply]
  exact (hprod _).symm.trans
    (exponentialProduct_eq_list_prod Exp (fun i => (b i : E)) x).symm

theorem local_exponential_regularity_of_dynkin
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {c n : ℕ} (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G,
      (List.ofFn (fun i => Exp (X i))).prod = Exp (finiteDynkinPolynomial coeff X))
    (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    ContMDiffAt (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, E)) ∞ (Exp ∘ b.equivFun.symm) 0 ∧
      HasMFDerivAt (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, E)) (Exp ∘ b.equivFun.symm) 0
        (tangentCombination (E := E) (fun i => (b i : E))) := by
  apply regularity_of_unit_parameter (E := E) (M := G) (basisDynkinParameter coeff b)
    (contDiff_basisDynkinParameter coeff b).contDiffAt
    (hasFDerivAt_basisDynkinParameter_zero hExp coeff hprod b)
    (basisDynkinParameter_zero coeff b)
  · rw [exponential_comp_basisDynkinParameter coeff hprod b]
    exact (hExp.contMDiff_exponentialProduct (fun i => (b i : E))).contMDiffAt
  · rw [exponential_comp_basisDynkinParameter coeff hprod b]
    exact hExp.hasMFDerivAt_exponentialProduct_zero (fun i => (b i : E))

end PolycyclicRecognition

end

end OAI
