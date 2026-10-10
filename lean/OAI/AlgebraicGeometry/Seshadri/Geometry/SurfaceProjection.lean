import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.SurfaceAffineCover

namespace OAI


                                           
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [Infinite K] [Fintype σ] {X : Scheme}

theorem surface_finite_projection [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p] [SmoothOfRelativeDimension 2 p]
    (L : LineBundle X) (s : σ → (O X ⟶ L.sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)] :
    ∃ t : Fin 3 → (O X ⟶ L.sheaf), ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
      IsFinite (sectionsMorphism
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) := by
  let k := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨v,hv⟩ := surface_three_sections p L s hs
  let t : Fin 3 → (O X ⟶ L.sheaf) := fun i => sectionCombination k s (v i)
  have ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤ := hv
  refine ⟨t,ht,?_⟩
  let f := sectionsMorphism k t ht
  let : IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k)) := by
    dsimp only [k]
    rw [toSpec_scalarMap]
    infer_instance
  let : IsProper f := sectionsMorphism_proper k t ht
  let : IsAffineHom f := by
    apply isAffineHom_of_forall_exists_isAffineOpen
    intro y
    have hy : y ∈ ⨆ i : Fin 3, Proj.basicOpen (PolyGrade K (Fin 3)) (MvPolynomial.X i) := by
      rw [projective_coordinate_cover]
      trivial
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hy
    refine ⟨Proj.basicOpen (PolyGrade K (Fin 3)) (MvPolynomial.X i),hi,
      Proj.isAffineOpen_basicOpen _ _ (poly_X_mem i) (by decide),?_⟩
    rw [show f = sectionsMorphism k t ht from rfl, sectionsMorphism_preimage]
    dsimp only [t]
    rw [← sectionsMorphism_hyperplane _ s hs]
    exact (Proj.isAffineOpen_basicOpen (PolyGrade K σ) _
      (linearEquation_homogeneous (v i)) (by decide)).preimage _
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance,inferInstance⟩

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames

theorem Surface.exists_finite_projection (S : Surface) (A : LineBundle S.scheme)
    (hA : A.IsAmple) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : Fin 3 → (O S.scheme ⟶ (A.pow n).sheaf),
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsFinite (sectionsMorphism (baseScalars S.structureMap) t ht) := by
  obtain ⟨n,hn,σ,hσ,s,hs,hclosed⟩ := S.ample_embedding A hA
  obtain ⟨t,ht,hf⟩ := @surface_finite_projection ℂ σ _ _ hσ S.scheme _ _
    S.structureMap _ _ (A.pow n) s hs hclosed
  exact ⟨n,hn,t,ht,hf⟩

end
end MaximalSeshadri.Geometry

end

end OAI
