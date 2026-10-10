import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.SmoothAffineRefinement
import OAI.AlgebraicGeometry.Seshadri.Intersection.SurfaceCurveDegree

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Projective MaximalSeshadri.Frames
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

variable {X Y : Scheme.{0}}

lemma topIso_baseScalars (p : X ⟶ Spec (CommRingCat.of ℂ)) (U : X.Opens) :
    U.topIso.hom.hom.comp (baseScalars (U.ι ≫ p)) = openScalars p U := by
  ext c
  rw [baseScalars_comp_actual]
  change (U.ι.appTop ≫ U.topIso.hom) (baseScalars p c) = _
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  have H := openScalars_restrict p (show U ≤ ⊤ from le_top)
  have hb : openScalars p ⊤ = baseScalars p := by
    unfold openScalars baseScalars
    change ((p.appTop ≫ X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens))))).hom.comp _ = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [hb] at H
  exact (congrArg (fun restriction : Γ(X,⊤) ⟶ Γ(X,U) => restriction (baseScalars p c))
    (X.presheaf.map_comp (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op
      (eqToHom U.ι_image_top.symm).op)).symm.trans
    (congrArg (fun scalars : ℂ →+* Γ(X,U) => scalars c) H)

def openTopAlgEquiv (p : X ⟶ Spec (CommRingCat.of ℂ)) (U : X.Opens) :
    letI : Algebra ℂ Γ(X,U) := (openScalars p U).toAlgebra
    letI : Algebra ℂ Γ(U.toScheme,⊤) := (baseScalars (U.ι ≫ p)).toAlgebra
    Γ(X,U) ≃ₐ[ℂ] Γ(U.toScheme,⊤) := by
  letI : Algebra ℂ Γ(X,U) := (openScalars p U).toAlgebra
  letI : Algebra ℂ Γ(U.toScheme,⊤) := (baseScalars (U.ι ≫ p)).toAlgebra
  refine { U.topIso.symm.commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro c
  apply (ConcreteCategory.bijective_of_isIso U.topIso.hom).injective
  change U.topIso.hom (U.topIso.inv (openScalars p U c)) =
    U.topIso.hom (baseScalars (U.ι ≫ p) c)
  rw [← CommRingCat.comp_apply, U.topIso.inv_hom_id]
  exact (congrArg (fun z : ℂ →+* Γ(X,U) => z c) (topIso_baseScalars p U)).symm

lemma chart_topIso_naturality (j : Y ⟶ X) (U : X.Opens) :
    U.topIso.hom ≫ j.app U ≫ (j ⁻¹ᵁ U).topIso.inv = (j ∣_ U).appTop := by
  have H := (arrowResLEAppIso j U (j ⁻¹ᵁ U) le_rfl).hom.w
  change U.topIso.hom ≫ j.appLE U (j ⁻¹ᵁ U) le_rfl =
    (j.resLE U (j ⁻¹ᵁ U) le_rfl).appTop ≫ (j ⁻¹ᵁ U).topIso.hom at H
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at H
  apply (cancel_mono (j ⁻¹ᵁ U).topIso.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using H

def structuralOpenChartMap (p : X ⟶ Spec (CommRingCat.of ℂ)) (j : Y ⟶ X) (U : X.Opens) :
    letI : Algebra ℂ Γ(X,U) := (openScalars p U).toAlgebra
    letI : Algebra ℂ Γ((j ⁻¹ᵁ U).toScheme,⊤) :=
      (baseScalars ((j ⁻¹ᵁ U).ι ≫ (j ≫ p))).toAlgebra
    Γ(X,U) →ₐ[ℂ] Γ((j ⁻¹ᵁ U).toScheme,⊤) := by
  letI : Algebra ℂ Γ(X,U) := (openScalars p U).toAlgebra
  letI : Algebra ℂ Γ((j ⁻¹ᵁ U).toScheme,⊤) :=
    (baseScalars ((j ⁻¹ᵁ U).ι ≫ (j ≫ p))).toAlgebra
  letI : Algebra ℂ Γ(U.toScheme,⊤) := (baseScalars (U.ι ≫ p)).toAlgebra
  exact (structuralChartMap p j U).comp (openTopAlgEquiv p U).toAlgHom

lemma structuralOpenChartMap_apply (p : X ⟶ Spec (CommRingCat.of ℂ))
    (j : Y ⟶ X) (U : X.Opens) (f : Γ(X,U)) :
    letI : Algebra ℂ Γ(X,U) := (openScalars p U).toAlgebra
    letI : Algebra ℂ Γ((j ⁻¹ᵁ U).toScheme,⊤) :=
      (baseScalars ((j ⁻¹ᵁ U).ι ≫ (j ≫ p))).toAlgebra
    structuralOpenChartMap p j U f = (j ⁻¹ᵁ U).topIso.inv (j.app U f) := by
  change (j ∣_ U).appTop (U.topIso.inv f) = _
  rw [← chart_topIso_naturality]
  simp only [CommRingCat.comp_apply]
  rw [U.topIso.inv_hom_id_apply]

lemma structuralOpenChartMap_ker (p : X ⟶ Spec (CommRingCat.of ℂ))
    (I : X.IdealSheafData) (U : X.affineOpens) :
    letI : Algebra ℂ Γ(X,U.1) := (openScalars p U.1).toAlgebra
    letI : Algebra ℂ Γ((I.subschemeι ⁻¹ᵁ U.1).toScheme,⊤) :=
      (baseScalars ((I.subschemeι ⁻¹ᵁ U.1).ι ≫ (I.subschemeι ≫ p))).toAlgebra
    RingHom.ker (structuralOpenChartMap p I.subschemeι U.1).toRingHom = I.ideal U := by
  ext t
  change structuralOpenChartMap p I.subschemeι U.1 t = 0 ↔ t ∈ I.ideal U
  rw [structuralOpenChartMap_apply, ← I.ker_subschemeι_app U]
  change (I.subschemeι ⁻¹ᵁ U.1).topIso.inv (I.subschemeι.app U.1 t) = 0 ↔
    I.subschemeι.app U.1 t = 0
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (I.subschemeι ⁻¹ᵁ U.1).topIso.inv).injective

lemma structuralOpenChartMap_surjective (p : X ⟶ Spec (CommRingCat.of ℂ))
    (j : Y ⟶ X) [IsClosedImmersion j] (U : X.affineOpens) :
    letI : Algebra ℂ Γ(X,U.1) := (openScalars p U.1).toAlgebra
    letI : Algebra ℂ Γ((j ⁻¹ᵁ U.1).toScheme,⊤) :=
      (baseScalars ((j ⁻¹ᵁ U.1).ι ≫ (j ≫ p))).toAlgebra
    Function.Surjective (structuralOpenChartMap p j U.1) := by
  let : Algebra ℂ Γ(X,U.1) := (openScalars p U.1).toAlgebra
  let : Algebra ℂ Γ((j ⁻¹ᵁ U.1).toScheme,⊤) :=
    (baseScalars ((j ⁻¹ᵁ U.1).ι ≫ (j ≫ p))).toAlgebra
  let : Algebra ℂ Γ(U.1.toScheme,⊤) := (baseScalars (U.1.ι ≫ p)).toAlgebra
  exact (structuralChartMap_surjective p j U).comp (openTopAlgEquiv p U.1).surjective

theorem IntegralCurve.nodal_branch_sum_le_degree_on_open (S : Surface)
    (C : IntegralCurve S) (A : LineBundle S.scheme)
    (hA : LineBundle.IsAmple S.scheme A)
    (L : LineBundle S.scheme) (s : O S.scheme ⟶ L.sheaf)
    (U : S.scheme.affineOpens) [Nonempty (C.embedding ⁻¹ᵁ U.1).toScheme]
    [IsDomain Γ(S.scheme,U.1)]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hR : ringKrullDim Γ(S.scheme,U.1) ≤ 2)
    (q : letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
      (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ))
    (hq : ∀ t, AnalyticAt ℂ (fun z => q z t) 0)
    (hjets : letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
      ∀ n : ℕ,
      RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
          (RingHom.ker (q 0))^n ∧
      Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom))
    (g : Γ(S.scheme,U.1)) (hg0 : g ≠ 0) [hgp : (Ideal.span {g}).IsPrime]
    (hker : RingHom.ker (C.embedding.app U.1).hom = Ideal.span {g})
    (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2)
    (hf : U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) ∉ Ideal.span {g}) :
    letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
    let f := U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))
    (((restrictX ℂ (bivariateTaylor q hq f)).order.toNat +
      (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat : ℕ) : ℤ) ≤
      curveDegree S L C := by
  let : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
  let : Algebra ℂ Γ((C.embedding ⁻¹ᵁ U.1).toScheme,⊤) :=
    (baseScalars ((C.embedding ⁻¹ᵁ U.1).ι ≫ (C.embedding ≫ S.structureMap))).toAlgebra
  let : IsAffine (C.embedding ⁻¹ᵁ U.1).toScheme := U.2.preimage C.embedding
  let : IsNoetherian (C.embedding ⁻¹ᵁ U.1).toScheme := {}
  let f := U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))
  let π := structuralOpenChartMap S.structureMap C.embedding U.1
  have hπker : RingHom.ker π.toRingHom = Ideal.span {g} := by
    ext t
    change π t = 0 ↔ t ∈ Ideal.span {g}
    rw [← hker]
    change structuralOpenChartMap S.structureMap C.embedding U.1 t = 0 ↔
      C.embedding.app U.1 t = 0
    rw [structuralOpenChartMap_apply]
    exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
      (C.embedding ⁻¹ᵁ U.1).topIso.inv).injective
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame C.embedding U.1 e s
  have hcoeff : π f = coefficient eF
      (restrictSection (C.embedding ⁻¹ᵁ U.1).ι (pullbackSection C.embedding s)) := by
    rw [he]
    change (C.embedding ∣_ U.1).appTop
      (U.1.topIso.inv (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)))) = _
    rw [U.1.topIso.hom_inv_id_apply]
  have hs : pullbackSection C.embedding s ≠ 0 := by
    intro hz
    apply hf
    rw [← hπker]
    change π f = 0
    rw [hcoeff, hz, restrictSection_zero, coefficient_zero]
  obtain ⟨σ,hσ,M,a,ha,hclosed⟩ := C.exists_projective_sections S A hA
  let := hσ
  let := hclosed
  exact projective_nodal_degree_bound (C.embedding ≫ S.structureMap) C.dimension
    a ha (L.pullback C.embedding) (pullbackSection C.embedding s) hs
    (C.embedding ⁻¹ᵁ U.1).ι eF hR q hq hjets f g hg0 u hu hu0 hg hf
    π (structuralOpenChartMap_surjective S.structureMap C.embedding U) hπker hcoeff

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
