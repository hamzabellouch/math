import OAI.GroupTheory.PolycyclicRecognition.Geometry.DynkinGlobalExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentLieModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialSmoothHom
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothHomLieDifferential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NormedLiePolynomial
import Mathlib.Algebra.Group.TransferInstance

namespace OAI

/-! # Polynomial group coordinates on a nilpotent algebra

Transport an existing model through its global exponential chart. The finite
BCH law makes the transported operations analytic. Its actual tangent bracket
is identified by differentiating the chart as a group homomorphism.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

class PolynomialExponentialCoordinates (L : Type*) [RealNormedLieAlgebra L]
    [FiniteDimensional ℝ L] where
  [group : Group L]
  [lieGroup : LieGroup (𝓘(ℝ, L)) ⊤ L]
  one_eq_zero : (1 : L) = 0
  inv_eq_neg : ∀ x : L, x⁻¹ = -x
  degree : ℕ
  coefficients : DynkinCoefficients degree 2
  mul_eq : ∀ x y : L, x * y = finiteDynkinPolynomial coefficients ![x, y]
  tangentEquiv : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, L)) L
  tangentEquiv_apply : ∀ x : L, tangentEquiv x = x

attribute [instance_reducible, instance] PolynomialExponentialCoordinates.group
attribute [instance] PolynomialExponentialCoordinates.lieGroup

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

theorem polynomialExponentialCoordinates_of_model
    (N : NilpotentLieModel L) (hnil : LieRing.IsNilpotent L)
    (dynkin : NilpotentDynkinExpansionInput N.modelSpace N.carrier) :
    Nonempty (PolynomialExponentialCoordinates L) := by
  let E := N.modelSpace
  let G := N.carrier
  let T := GroupLieAlgebra (𝓘(ℝ, E)) G
  let : NormedAddCommGroup T := by change NormedAddCommGroup E; exact inferInstance
  let : NormedSpace ℝ T := by change NormedSpace ℝ E; exact inferInstance
  let Exp : T → G := groupExponential
  have hExp : IsGroupExponential Exp := groupExponential_isGroupExponential
  have hn : LieRing.IsNilpotent T := N.tangent_nilpotent hnil
  obtain ⟨chart, hchart⟩ := nilpotentGlobalExponentialChart_of_dynkin dynkin Exp hExp hn
  let C : L ≃ₜ G := N.equiv.toLinearEquiv.toContinuousLinearEquiv.toHomeomorph.trans chart
  have hC (x : L) : C x = Exp (N.equiv x) := hchart _
  let : Group L := C.toEquiv.group
  have hmul (x y : L) : C (x * y) = C x * C y := C.apply_symm_apply _
  have hone : (1 : L) = 0 := by
    apply C.injective
    rw [show C 1 = (1 : G) from C.apply_symm_apply _]
    rw [hC, map_zero, hExp.map_zero]
  have hinv (x : L) : x⁻¹ = -x := by
    apply C.injective
    rw [show C (x⁻¹) = (C x)⁻¹ from C.apply_symm_apply _]
    rw [hC x, hC (-x), map_neg, hExp.map_neg]
  obtain ⟨c, hc⟩ := (LieModule.isNilpotent_iff ℝ T T).mp hn
  obtain ⟨coeff, _, hprod⟩ := dynkin Exp hExp c hc 2
  have hpoly (x y : L) : x * y = finiteDynkinPolynomial coeff ![x, y] := by
    apply C.injective
    rw [hmul, hC, hC, hC]
    have he := finiteDynkinPolynomial_map N.equiv.toLieHom coeff ![x, y]
    change N.equiv (finiteDynkinPolynomial coeff ![x, y]) = _ at he
    rw [he]
    have hX : (fun i => N.equiv.toLieHom (![x, y] i)) = ![N.equiv x, N.equiv y] := by
      funext i
      fin_cases i <;> rfl
    rw [hX]
    have hp := hprod ![N.equiv x, N.equiv y]
    simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      mul_one, Matrix.cons_val_zero, Matrix.cons_val_succ] using hp
  let : LieGroup (𝓘(ℝ, L)) ⊤ L :=
    { toIsManifold := inferInstance
      contMDiff_mul := by
        have hp : ContDiff ℝ ⊤ (fun p : L × L =>
            finiteDynkinPolynomial coeff ![p.1, p.2]) := by
          apply contDiff_normed_finiteDynkinPolynomial
          intro i
          fin_cases i
          · exact contDiff_fst
          · exact contDiff_snd
        have heq : (fun p : L × L => p.1 * p.2) =
            (fun p : L × L => finiteDynkinPolynomial coeff ![p.1, p.2]) := by
          funext p; exact hpoly _ _
        rw [heq]
        exact hp.comp_contMDiff (contMDiff_fst.prodMk_space contMDiff_snd)
      contMDiff_inv := by
        have heq : (fun x : L => x⁻¹) = fun x : L => -x := funext hinv
        rw [heq]
        exact contDiff_neg.contMDiff }
  have hidentity : IsGroupExponential (fun x : GroupLieAlgebra (𝓘(ℝ, L)) L => (x : L)) := by
    refine ⟨hone.symm, ?_, ?_⟩
    · intro v s t
      apply C.injective
      have hmap (w : L) (r u : ℝ) : C ((r + u) • w) = C (r • w * u • w) := by
        rw [hmul, hC, hC, hC, map_smul, map_smul, map_smul]
        exact hExp.map_add_smul _ _ _
      exact hmap (show L from v) s t
    · intro v
      have hd := ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const (show L from v)).hasMFDerivAt
      exact hd
  let φ : L →* G :=
    { C.toEquiv with
      map_one' := C.apply_symm_apply _
      map_mul' := hmul }
  have hcompat (v : L) : φ v = Exp (N.equiv v) := hC v
  have hφ := contMDiff_of_exponential_compatibility hidentity hExp φ C.continuous
    N.equiv.toLinearMap hcompat
  have hdiff (v : L) : homLieDifferential φ hφ v = N.equiv v :=
    mfderiv_eq_of_exponential_compatibility hidentity hExp φ
      (hφ.mdifferentiable (by simp)) N.equiv.toLinearMap hcompat v
  let f := N.equiv.symm.toLieHom.comp (homLieDifferential φ hφ)
  have hf (v : GroupLieAlgebra (𝓘(ℝ, L)) L) : f v = (v : L) := by
    change N.equiv.symm (homLieDifferential φ hφ v) = v
    exact (congrArg N.equiv.symm (hdiff (v : L))).trans (N.equiv.symm_apply_apply (v : L))
  let e := LieEquiv.ofBijective f
    ⟨fun x y h => by exact (hf x).symm.trans (h.trans (hf y)), fun y => ⟨y, hf y⟩⟩
  refine ⟨{ group := inferInstance
            lieGroup := inferInstance
            one_eq_zero := hone
            inv_eq_neg := hinv
            degree := c
            coefficients := coeff
            mul_eq := hpoly
            tangentEquiv := e.symm
            tangentEquiv_apply := ?_ }⟩
  intro x
  have he := e.apply_symm_apply x
  change f (e.symm x) = x at he
  exact (hf (e.symm x)).symm.trans he

end PolycyclicRecognition

end

end OAI
