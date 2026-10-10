import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.HyperplaneAvoidance
import OAI.AlgebraicGeometry.Seshadri.Geometry.CurveFiniteMap

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

theorem curve_exists_finite_pencil [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) {M : X.Modules}
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (i : σ) (hne : (SectionOpens.isoOpen (s i) : Set X).Nonempty)
    (hproper : SectionOpens.isoOpen (s i) ≠ ⊤) :
    ∃ t : Bool → (O X ⟶ M), ∃ ht : (⨆ b, SectionOpens.isoOpen (t b)) = ⊤,
      t false = s i ∧ IsFinite (sectionsMorphism
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) := by
  classical
  let k := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let U := SectionOpens.isoOpen (s i)
  let Z : Set X := (U : Set X)ᶜ
  have hz : Z.Finite := proper_closed_finite_of_dimension_one hd U.isOpen.isClosed_compl (by
    intro he
    obtain ⟨x,hx⟩ := hne
    have : x ∈ Z := he ▸ Set.mem_univ x
    exact this hx)
  let : Finite Z := hz.to_subtype
  obtain ⟨v,hv⟩ := exists_section_avoiding k s hs ((↑) : Z → X)
  let t : Bool → (O X ⟶ M) := fun b => if b then sectionCombination k s v else s i
  have ht : (⨆ b, SectionOpens.isoOpen (t b)) = ⊤ := by
    apply top_unique
    intro x hx
    by_cases h : x ∈ U
    · apply Opens.mem_iSup.mpr
      exact ⟨false, h⟩
    · apply Opens.mem_iSup.mpr
      exact ⟨true, hv ⟨x,h⟩⟩
  let f := sectionsMorphism k t ht
  have hf : IsFinite f := by
    let : IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k)) := by
      dsimp only [k]
      rw [toSpec_scalarMap]
      infer_instance
    let : IsProper f := sectionsMorphism_proper k t ht
    apply proper_curve_nonconstant_isFinite f hd
    obtain ⟨a,ha⟩ := hne
    obtain ⟨b,hb⟩ : ∃ b : X, b ∉ U := by
      by_contra h
      apply hproper
      apply top_unique
      intro x hx
      exact Classical.not_not.mp (fun hx => h ⟨x,hx⟩)
    refine ⟨a,b,fun he => ?_⟩
    have hp : f ⁻¹ᵁ Proj.basicOpen (PolyGrade K Bool) (MvPolynomial.X false) = U :=
      sectionsMorphism_preimage k t ht false
    have ha' : a ∈ f ⁻¹ᵁ Proj.basicOpen (PolyGrade K Bool) (MvPolynomial.X false) := by
      rw [hp]
      exact ha
    have hb' : b ∈ U := by
      rw [← hp]
      change f b ∈ Proj.basicOpen (PolyGrade K Bool) (MvPolynomial.X false)
      rw [← he]
      exact ha'
    exact hb hb'
  exact ⟨t,ht,rfl,hf⟩

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
