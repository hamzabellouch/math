import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.FiniteIntersection
import OAI.AlgebraicGeometry.Seshadri.Cohomology.ProjectiveCurveCohomology
import OAI.AlgebraicGeometry.Seshadri.Intersection.IntersectionEuler

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MaximalSeshadri.Projective MaximalSeshadri.Frames

variable {X : Scheme.{0}}

def cartierKernelLine (I : X.IdealSheafData)
    (hI : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ r : Γ(X,U.1),
      IsRegular r ∧ I.ideal U = Ideal.span {r}) : LineBundle X where
  sheaf := IdealModule.closedModule I
  locallyRankOne x := by
    obtain ⟨U,hx,r,hr,he⟩ := hI x
    let e := U.1.topIso.commRingCatIsoToRingEquiv
    have hreg : IsLeftRegular (e.symm r) := by
      intro a b hab
      apply e.injective
      apply hr.1
      simpa only [map_mul, e.apply_symm_apply] using congrArg e hab
    refine ⟨U.1,hx,IdealModule.frame_restriction I U.1.ι (e.symm r) ?_ hreg⟩
    rw [IdealPullback.comap_ι_top,he,Ideal.map_span,Set.image_singleton]
    rfl

lemma cartier_ideal_ne_bot [IsIntegral X] (I : X.IdealSheafData)
    (hI : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ r : Γ(X,U.1),
      IsRegular r ∧ I.ideal U = Ideal.span {r}) : I ≠ ⊥ := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U,hx,r,hr,he⟩ := hI x
  let : Nonempty U.1 := ⟨⟨x,hx⟩⟩
  intro hz
  have hzero : r = 0 := by
    have hm : r ∈ I.ideal U := he ▸ Ideal.subset_span (by simp)
    simpa [hz] using hm
  exact (isRegular_iff_ne_zero.mp hr) hzero

theorem projective_curve_cartier_euler_length {σ : Type} [Fintype σ]
    [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) s hs)]
    (I : X.IdealSheafData)
    (hI : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ r : Γ(X,U.1),
      IsRegular r ∧ I.ideal U = Ideal.span {r}) :
    eulerCharacteristic p 1 (structureSheaf X) -
      eulerCharacteristic p 1 (IdealModule.closedModule I) =
      letI : Algebra ℂ Γ(I.subscheme,⊤) := (baseScalars (I.subschemeι ≫ p)).toAlgebra;
      (Module.finrank ℂ Γ(I.subscheme,⊤) : ℤ) := by
  let J := cartierKernelLine I hI
  let OX : LineBundle X := ⟨structureSheaf X,fun _ =>
    ⟨⊤,trivial,⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩⟩
  let : Finite I.subscheme := finite_subscheme_of_curve p hd.le I (cartier_ideal_ne_bot I hI)
  let : J.sheaf.IsQuasicoherent := J.quasicoherent
  let : Subsingleton (cohomology (IdealModule.idealModule I.subschemeι) 2) :=
    ⟨fun x y => (projective_curve_ext_zero p hd s hs J.sheaf 0 x).trans
      (projective_curve_ext_zero p hd s hs J.sheaf 0 y).symm⟩
  exact FiniteSupport.closed_ideal_euler_difference I.subschemeι p 1
    (fun n _ => projective_curve_cohomology_finite p hd s hs J n)
    (fun n _ => projective_curve_cohomology_finite p hd s hs OX n)
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
