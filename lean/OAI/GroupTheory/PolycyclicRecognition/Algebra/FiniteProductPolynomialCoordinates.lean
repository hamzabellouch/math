import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialExponentialCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteProductGlobalChart
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentLieModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialSmoothHom
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothHomLieDifferential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NormedLiePolynomial
import Mathlib.Algebra.Group.TransferInstance

namespace OAI

/-! # Polynomial exponential coordinates from a finite product law

A concrete representation may provide a polynomial law with a degree larger
than the Lie nilpotency class. That is enough for the global coordinate construction.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

theorem polynomialExponentialCoordinates_equiv_of_finite_products
    (N : NilpotentLieModel L) (hnil : LieRing.IsNilpotent L)
    {c : ℕ} (coefficients : (n : ℕ) → DynkinCoefficients c n)
    (products : ∀ n (X : Fin n → GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier),
      (List.ofFn (fun i => groupExponential (X i))).prod =
        groupExponential (finiteDynkinPolynomial (coefficients n) X)) :
    ∃ P : PolynomialExponentialCoordinates L,
      ∃ e : @MulEquiv L N.carrier P.group.toMul N.group.toMul,
        ∀ x, e x = groupExponential (N.equiv x) := by
  let E := N.modelSpace
  let G := N.carrier
  let T := GroupLieAlgebra (𝓘(ℝ, E)) G
  let : NormedAddCommGroup T := by change NormedAddCommGroup E; exact inferInstance
  let : NormedSpace ℝ T := by change NormedSpace ℝ E; exact inferInstance
  let Exp : T → G := groupExponential
  have hExp : IsGroupExponential Exp := groupExponential_isGroupExponential
  have hn : LieRing.IsNilpotent T := N.tangent_nilpotent hnil
  obtain ⟨chart, hchart⟩ := globalExponentialChart_of_finite_products Exp hExp hn coefficients products
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
  let coeff := coefficients 2
  have hprod := products 2
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
      let w : L := v
      change (s + t) • w = (s • w) * (t • w)
      apply C.injective
      rw [hmul, hC, hC, hC, map_smul, map_smul, map_smul]
      exact hExp.map_add_smul _ _ _
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
    exact (congrArg N.equiv.symm (hdiff v)).trans (N.equiv.symm_apply_apply v)
  let e := LieEquiv.ofBijective f
    ⟨fun x y h => by
      have hxy : (x : L) = (y : L) := (hf x).symm.trans (h.trans (hf y))
      exact hxy, fun y => ⟨y, hf y⟩⟩
  let P : PolynomialExponentialCoordinates L :=
          { group := inferInstance
            lieGroup := inferInstance
            one_eq_zero := hone
            inv_eq_neg := hinv
            degree := c
            coefficients := coeff
            mul_eq := hpoly
            tangentEquiv := e.symm
            tangentEquiv_apply := by
              intro x
              have he := e.apply_symm_apply x
              change f (e.symm x) = x at he
              rwa [hf] at he }
  exact ⟨P, { C.toEquiv with map_mul' := hmul }, hC⟩

/-- Forgetting the exponential chart recovers the original existence result. -/
theorem polynomialExponentialCoordinates_of_finite_products
    (N : NilpotentLieModel L) (hnil : LieRing.IsNilpotent L)
    {c : ℕ} (coefficients : (n : ℕ) → DynkinCoefficients c n)
    (products : ∀ n (X : Fin n → GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier),
      (List.ofFn (fun i => groupExponential (X i))).prod =
        groupExponential (finiteDynkinPolynomial (coefficients n) X)) :
    Nonempty (PolynomialExponentialCoordinates L) := by
  obtain ⟨P, _, _⟩ := polynomialExponentialCoordinates_equiv_of_finite_products
    N hnil coefficients products
  exact ⟨P⟩

end PolycyclicRecognition

end

end OAI
