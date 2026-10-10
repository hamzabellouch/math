import Mathlib

namespace OAI

section
noncomputable section
                                           

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}

def openScalars (g : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) : K →+* Γ(X, U) :=
  (g.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

lemma openScalars_restrict (g : X ⟶ Spec (CommRingCat.of K)) {U V : X.Opens}
    (e : U ≤ V) :
    (X.presheaf.map (homOfLE e).op).hom.comp (openScalars g V) = openScalars g U := by
  exact congrArg (fun morphism : Γ(Spec (CommRingCat.of K), ⊤) ⟶ Γ(X, U) =>
    morphism.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    (Scheme.Hom.appLE_map g (show V ≤ g ⁻¹ᵁ ⊤ from by simp) (homOfLE e).op)

lemma spec_openScalars (g : X ⟶ Spec (CommRingCat.of K)) (U : X.affineOpens) :
    Spec.map (CommRingCat.ofHom (openScalars g U.1)) = U.2.fromSpec ≫ g := by
  rw [openScalars, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom,
    CommRingCat.ofHom_hom]
  rw [← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top _) U.2 _

theorem exists_standard_smooth_affine_inside
    (g : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n g]
    (W : X.Opens) (x : X) (hx : x ∈ W) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧
      RingHom.IsStandardSmoothOfRelativeDimension n (openScalars g U.1) := by
  obtain ⟨B, hB, V, hV, hxV, e, hg⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := n) (f := g) x
  have hBtop : B = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = g x := Subsingleton.elim _ _
    rw [hy]
    exact e hxV
  subst B
  let e₀ : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    RingEquiv.ofBijective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)
  have hstd : RingHom.IsStandardSmoothOfRelativeDimension n (openScalars g V) := by
    convert hg.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e₀) using 1
    rfl
  obtain ⟨f, hfW, hxf⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ hxV
  refine ⟨⟨X.basicOpen f, hV.basicOpen f⟩, hxf, hfW, ?_⟩
  let : IsLocalization.Away f Γ(X, X.basicOpen f) := hV.isLocalization_basicOpen f
  have hs := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
    (Γ(X, X.basicOpen f)) f (openScalars g V) hstd
  convert hs using 1
  exact (openScalars_restrict g (X.basicOpen_le f)).symm

end
end MaximalSeshadri.ProjectiveBertini


end
end

end OAI
