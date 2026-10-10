import OAI.NumberTheory.PiExponent.Geometry.CurveGeometricFunctionField
import OAI.NumberTheory.PiExponent.LocalAlgebra.IntegralAffineOpenDimension
import OAI.NumberTheory.PiExponent.LocalAlgebra.OpenIsoFunctionField

namespace OAI

noncomputable section
namespace PiExponent.CurveImageAffineCoordinates
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {C X : Scheme.{0}} [IsIntegral C]
variable {ι : Type}

theorem preimage_surjective {R S : CommRingCat}
    (q : Spec S ⟶ Spec R) [IsClosedImmersion q] :
    Function.Surjective (Spec.preimage q) := by
  have he : Spec.preimage q = (Scheme.ΓSpecIso R).inv ≫ q.appTop ≫
      (Scheme.ΓSpecIso S).hom := by
    have h : Spec.preimage q = (Scheme.ΓSpecIso R).inv ≫
        (Spec.map (Spec.preimage q)).appTop ≫ (Scheme.ΓSpecIso S).hom := by
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    simpa only [Spec.map_preimage] using h
  rw [he]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).hom).surjective.comp
    ((q.app_surjective ⊤ (isAffineOpen_top _)).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).surjective)

def presentation (p : C ⟶ Spec (.of ℂ)) (U : C.affineOpens)
    (q : Spec Γ(C,U.1) ⟶ Spec (.of (MvPolynomial ι ℂ)))
    (hq : q ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ)) =
      U.2.fromSpec ≫ p) :
    letI := IntegralAffineOpenDimension.chartAlgebra p U
    MvPolynomial ι ℂ →ₐ[ℂ] Γ(C,U.1) := by
  letI := IntegralAffineOpenDimension.chartAlgebra p U
  refine ⟨(Spec.preimage q).hom,?_⟩
  intro c
  have h : CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ) ≫
      Spec.preimage q = Spec.preimage (U.2.fromSpec ≫ p) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    exact hq
  exact congrArg (fun φ : CommRingCat.of ℂ ⟶ Γ(C,U.1) => φ c) h

def coordinates (U : C.affineOpens) [Nonempty U.1]
    (q : Spec Γ(C,U.1) ⟶ Spec (.of (MvPolynomial ι ℂ))) : ι → C.functionField :=
  fun i => C.germToFunctionField U.1 ((Spec.preimage q) (MvPolynomial.X i))

theorem field_properties [Finite ι] (p : C ⟶ Spec (.of ℂ)) [LocallyOfFiniteType p]
    (hdim : topologicalKrullDim C = 1) (U : C.affineOpens) [Nonempty U.1]
    (q : Spec Γ(C,U.1) ⟶ Spec (.of (MvPolynomial ι ℂ))) [IsClosedImmersion q]
    (hq : q ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ)) =
      U.2.fromSpec ≫ p) :
    letI := IntegralAffineOpenDimension.functionFieldAlgebra p
    Algebra.EssFiniteType ℂ C.functionField ∧ Algebra.trdeg ℂ C.functionField = 1 ∧
      IntermediateField.adjoin ℂ (Set.range (coordinates U q)) = ⊤ := by
  let := IntegralAffineOpenDimension.chartAlgebra p U
  let := IntegralAffineOpenDimension.functionFieldAlgebra p
  let := IntegralAffineOpenDimension.chart_functionField_scalarTower p U
  let := functionField_isFractionRing_of_isAffineOpen C U.1 U.2
  have hdimA : ringKrullDim Γ(C,U.1) = 1 :=
    (IntegralAffineOpenDimension.affine_ring_dimension_eq p U).trans hdim
  exact CurveGeometricFunctionField.of_surjective_coordinates ℂ Γ(C,U.1) C.functionField
    (presentation p U q hq) (preimage_surjective q) hdimA

theorem coordinates_generic_map
    (p : C ⟶ Spec (.of ℂ)) (U : C.affineOpens) [Nonempty U.1]
    (q : Spec Γ(C,U.1) ⟶ Spec (.of (MvPolynomial ι ℂ)))
    (hq : q ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ)) =
      U.2.fromSpec ≫ p)
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) (i : C ⟶ X)
    (hchart : q ≫ j = U.2.fromSpec ≫ i) :
    letI := IntegralAffineOpenDimension.functionFieldAlgebra p
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (coordinates U q)).toRingHom) ≫ j =
      C.fromSpecStalk (genericPoint C) ≫ i := by
  let := IntegralAffineOpenDimension.chartAlgebra p U
  let := IntegralAffineOpenDimension.functionFieldAlgebra p
  let := IntegralAffineOpenDimension.chart_functionField_scalarTower p U
  have he : (MvPolynomial.aeval (coordinates U q)).toRingHom =
      (C.germToFunctionField U.1).hom.comp (Spec.preimage q).hom := by
    apply congrArg AlgHom.toRingHom
      (show MvPolynomial.aeval (coordinates U q) =
        (IsScalarTower.toAlgHom ℂ Γ(C,U.1) C.functionField).comp (presentation p U q hq) from ?_)
    apply MvPolynomial.algHom_ext
    intro a
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
    rfl
  rw [he, ← CommRingCat.hom_comp, CommRingCat.ofHom_hom, Spec.map_comp,
    Spec.map_preimage, Category.assoc, hchart, ← Category.assoc,
    IntegralAffineOpenDimension.germToFunctionField_fromSpec]

theorem transport_field_properties {F E : Type} [Field F] [Field E]
    [Algebra ℂ F] [Algebra ℂ E] [Algebra.EssFiniteType ℂ F]
    (e : F ≃ₐ[ℂ] E) (x : ι → F)
    (hd : Algebra.trdeg ℂ F = 1)
    (hx : IntermediateField.adjoin ℂ (Set.range x) = ⊤) :
    Algebra.EssFiniteType ℂ E ∧ Algebra.trdeg ℂ E = 1 ∧
      IntermediateField.adjoin ℂ (Set.range (e ∘ x)) = ⊤ := by
  refine ⟨Algebra.EssFiniteType.of_surjective e.toAlgHom e.surjective,
    e.trdeg_eq.symm.trans hd, ?_⟩
  rw [Set.range_comp]
  change IntermediateField.adjoin ℂ (e.toAlgHom '' Set.range x) = ⊤
  rw [← IntermediateField.adjoin_map ℂ (Set.range x) e.toAlgHom, hx,
    ← AlgHom.fieldRange_eq_map]
  exact e.fieldRange_eq_top

def fieldAlgEquiv {D : Scheme.{0}} [IsIntegral D]
    (pC : C ⟶ Spec (.of ℂ)) (pD : D ⟶ Spec (.of ℂ))
    (e : C.functionField ≅ D.functionField)
    (he : Spec.map e.hom ≫ C.fromSpecStalk (genericPoint C) ≫ pC =
      D.fromSpecStalk (genericPoint D) ≫ pD) :
    letI := IntegralAffineOpenDimension.functionFieldAlgebra pC
    letI := IntegralAffineOpenDimension.functionFieldAlgebra pD
    C.functionField ≃ₐ[ℂ] D.functionField := by
  letI := IntegralAffineOpenDimension.functionFieldAlgebra pC
  letI := IntegralAffineOpenDimension.functionFieldAlgebra pD
  refine { e.commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro c
  have h : Spec.preimage (C.fromSpecStalk (genericPoint C) ≫ pC) ≫ e.hom =
      Spec.preimage (D.fromSpecStalk (genericPoint D) ≫ pD) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    exact he
  exact congrArg (fun φ : CommRingCat.of ℂ ⟶ D.functionField => φ c) h

end PiExponent.CurveImageAffineCoordinates

end

end OAI
