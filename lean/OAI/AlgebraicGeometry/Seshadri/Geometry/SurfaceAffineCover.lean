import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.SectionDimension
import OAI.AlgebraicGeometry.Seshadri.Intersection.AmpleCurveDegree

namespace OAI


                                            
section

namespace MaximalSeshadri.Geometry
open TopologicalSpace Set

theorem exists_finite_test_set_of_dimension_one
    (X : Type*) [TopologicalSpace X] [T0Space X] [NoetherianSpace X]
    (hd : topologicalKrullDim X ≤ 1) :
    ∃ T : Set X, T.Finite ∧ ∀ U : Set X, IsOpen U → T ⊆ U → Uᶜ.Finite := by
  classical
  obtain ⟨F,hF,hFc,hFi,hFcover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_univ : IsClosed (univ : Set X))
  let x (C : F) : X := (hFi C.1 C.2).nonempty.choose
  have hx (C : F) : x C ∈ C.1 := (hFi C.1 C.2).nonempty.choose_spec
  let : Finite F := hF.to_subtype
  refine ⟨Set.range x, Set.finite_range x, ?_⟩
  intro U hU hTU
  have hpiece (C : F) : (C.1 ∩ Uᶜ).Finite := by
    let : IrreducibleSpace C.1 := Subtype.irreducibleSpace (hFi C.1 C.2)
    have hdC : topologicalKrullDim C.1 ≤ 1 :=
      (topologicalKrullDim_subspace_le X C.1).trans hd
    have hz : ((Subtype.val : C.1 → X) ⁻¹' Uᶜ).Finite := by
      apply proper_closed_finite_of_dimension_one hdC
        (hU.isClosed_compl.preimage continuous_subtype_val)
      intro he
      have hm : (⟨x C,hx C⟩ : C.1) ∈ (Subtype.val : C.1 → X) ⁻¹' Uᶜ := by
        rw [he]; trivial
      exact hm (hTU (Set.mem_range_self C))
    have he : C.1 ∩ Uᶜ = Subtype.val '' ((Subtype.val : C.1 → X) ⁻¹' Uᶜ) := by
      ext y
      constructor
      · intro hy
        exact ⟨⟨y,hy.1⟩,hy.2,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨y.2,hy⟩
    rw [he]
    exact hz.image _
  have he : Uᶜ = ⋃ C : F, C.1 ∩ Uᶜ := by
    ext y
    constructor
    · intro hy
      have hyF : y ∈ ⋃₀ F := hFcover ▸ Set.mem_univ y
      obtain ⟨C,hC,hyC⟩ := hyF
      exact Set.mem_iUnion.mpr ⟨⟨C,hC⟩,hyC,hy⟩
    · intro hy
      obtain ⟨C,hyC⟩ := Set.mem_iUnion.mp hy
      exact hyC.2
  rw [he]
  exact Set.finite_iUnion hpiece

end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [Infinite K] [Fintype σ] {X : Scheme}

omit [Infinite K] in
lemma sectionIdeal_support_eq {M : X.Modules} (k : K →+* Γ(X,⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → K) :
    ((sectionIdeal k s hs v).support : Set X) =
      (SectionOpens.isoOpen (sectionCombination k s v) : Set X)ᶜ := by
  rw [sectionIdeal, Scheme.IdealSheafData.support_comap]
  simp only [ambientHyperplane, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_preimage, Opens.coe_compl]
  rw [← sectionsMorphism_hyperplane k s hs]
  rfl

theorem surface_three_sections [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 p]
    (L : LineBundle X) (s : σ → (O X ⟶ L.sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)] :
    ∃ v : Fin 3 → (σ → K),
      (⨆ i, SectionOpens.isoOpen (sectionCombination (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s (v i))) = ⊤ := by
  classical
  let k : K →+* Γ(X,⊤) :=
    p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨v₀,hv₀⟩ := exists_section_avoiding k s hs (fun _ : Unit => x)
  have hne : sectionCombination k s v₀ ≠ 0 :=
    section_ne_zero_of_mem_isoOpen L _ x (hv₀ ())
  let I : X.IdealSheafData := sectionIdeal k s hs v₀
  let U₀ := SectionOpens.isoOpen (sectionCombination k s v₀)
  have hsupport : (I.support : Set X) = (U₀ : Set X)ᶜ := sectionIdeal_support_eq k s hs v₀
  have hbase : sectionsMorphism k s hs ≫ projectiveToSpec = p := by
    change _ ≫ projectiveBase = p
    rw [sectionsMorphism_over, toSpec_scalarMap]
  have hd : topologicalKrullDim I.subscheme ≤ 1 :=
    sectionIdeal_dimension_le_one p (sectionsMorphism k s hs) hbase L k s hs v₀ hne
  let : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
  let : IsNoetherian I.subscheme := {}
  obtain ⟨T,hT,hdetect⟩ := exists_finite_test_set_of_dimension_one I.subscheme hd
  let : Finite T := hT.to_subtype
  obtain ⟨v₁,hv₁⟩ := exists_section_avoiding k s hs (fun z : T => I.subschemeι z.1)
  let U₁ := SectionOpens.isoOpen (sectionCombination k s v₁)
  have hfin : ((I.subschemeι ⁻¹ᵁ U₁ : I.subscheme.Opens) : Set I.subscheme)ᶜ.Finite := by
    apply hdetect _ (I.subschemeι ⁻¹ᵁ U₁).isOpen
    intro z hz
    exact hv₁ ⟨z,hz⟩
  let Z : Set X := I.subschemeι '' (((I.subschemeι ⁻¹ᵁ U₁ : I.subscheme.Opens) : Set I.subscheme)ᶜ)
  have hZ : Z.Finite := hfin.image _
  let : Finite Z := hZ.to_subtype
  obtain ⟨v₂,hv₂⟩ := exists_section_avoiding k s hs ((↑) : Z → X)
  refine ⟨![v₀,v₁,v₂], top_unique ?_⟩
  intro y hy
  apply Opens.mem_iSup.mpr
  by_cases hy₀ : y ∈ U₀
  · exact ⟨0,hy₀⟩
  by_cases hy₁ : y ∈ U₁
  · exact ⟨1,hy₁⟩
  have hyI : y ∈ I.support := by
    change y ∈ (I.support : Set X)
    rw [hsupport]
    exact hy₀
  obtain ⟨z,hz⟩ := (I.range_subschemeι ▸ hyI : y ∈ Set.range I.subschemeι)
  have hyZ : y ∈ Z := ⟨z, by change I.subschemeι z ∉ U₁; rwa [hz], hz⟩
  exact ⟨2,hv₂ ⟨y,hyZ⟩⟩

theorem projective_surface_three_affine_opens [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 p]
    (L : LineBundle X) (s : σ → (O X ⟶ L.sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)] :
    ∃ U : Fin 3 → X.Opens, (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ := by
  obtain ⟨v,hv⟩ := surface_three_sections p L s hs
  refine ⟨fun i => SectionOpens.isoOpen (sectionCombination (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s (v i)), ?_, hv⟩
  intro i
  dsimp only
  rw [← sectionsMorphism_hyperplane _ s hs]
  exact (Proj.isAffineOpen_basicOpen (PolyGrade K σ) _
    (linearEquation_homogeneous (v i)) (by decide)).preimage _

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames

theorem Surface.three_affine_opens (S : Surface) (A : LineBundle S.scheme)
    (hA : LineBundle.IsAmple S.scheme A) :
    ∃ U : Fin 3 → S.scheme.Opens, (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ := by
  obtain ⟨n,hn,σ,hσ,s,hs,hclosed⟩ := S.ample_embedding A hA
  exact @projective_surface_three_affine_opens ℂ σ _ _ hσ S.scheme _ _
    S.structureMap _ (A.pow n) s hs hclosed

end
end MaximalSeshadri.Geometry

end

end OAI
