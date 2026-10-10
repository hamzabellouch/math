import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.CurvePencil

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [Infinite K] [Fintype σ] {X : Scheme}

omit [Infinite K] in
lemma proper_affine_dimension_zero [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p] : topologicalKrullDim X ≤ 0 := by
  let : IsFinite p := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance,inferInstance⟩
  let y : Spec (CommRingCat.of K) := ⟨⊥, Ideal.isPrime_bot⟩
  have he : p ⁻¹' ({y} : Set (Spec (CommRingCat.of K))) = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have h := p.isDiscrete_preimage_singleton y
  rw [he] at h
  let : DiscreteTopology X := isDiscrete_univ_iff.mp h
  exact topologicalKrullDim_zero_of_discreteTopology X

theorem projective_curve_finite_pencil [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)] :
    ∃ t : Bool → (O X ⟶ M), ∃ ht : (⨆ b, SectionOpens.isoOpen (t b)) = ⊤,
      IsFinite (sectionsMorphism
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) := by
  let k := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hx : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := hs ▸ trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hx
  have hne : (SectionOpens.isoOpen (s i) : Set X).Nonempty := ⟨x,hi⟩
  have hproper : SectionOpens.isoOpen (s i) ≠ ⊤ := by
    intro he
    have hA := (Proj.isAffineOpen_basicOpen (PolyGrade K σ) _ (poly_X_mem i)
      (by decide)).preimage (sectionsMorphism k s hs)
    rw [sectionsMorphism_preimage, he] at hA
    let : IsAffine (⊤ : X.Opens).toScheme := hA
    let : IsAffine X := .of_isIso X.topIso.inv
    have hdim := proper_affine_dimension_zero p
    rw [hd] at hdim
    norm_num at hdim
  obtain ⟨t,ht,_,hf⟩ := curve_exists_finite_pencil p hd.le s hs i hne hproper
  exact ⟨t,ht,hf⟩
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
