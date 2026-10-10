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

theorem surface_three_sections_through [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 p]
    (L : LineBundle X) (s : σ → (O X ⟶ L.sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)] :
    ∀ x : X, ∃ v : Fin 3 → (σ → K),
      (⨆ i, SectionOpens.isoOpen (sectionCombination (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s (v i))) = ⊤ ∧
      ∀ i, x ∈ SectionOpens.isoOpen (sectionCombination (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s (v i)) := by
  classical
  let k := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  intro x
  obtain ⟨v₀,hv₀⟩ := exists_section_avoiding k s hs (fun _ : Unit => x)
  have hne : sectionCombination k s v₀ ≠ 0 :=
    section_ne_zero_of_mem_isoOpen L _ x (hv₀ ())
  let I := sectionIdeal k s hs v₀
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
  obtain ⟨v₁,hv₁⟩ := exists_section_avoiding k s hs (fun z : Option T => z.elim x (fun z => I.subschemeι z.1))
  let U₁ := SectionOpens.isoOpen (sectionCombination k s v₁)
  have hfin : ((I.subschemeι ⁻¹ᵁ U₁ : I.subscheme.Opens) : Set I.subscheme)ᶜ.Finite := by
    apply hdetect _ (I.subschemeι ⁻¹ᵁ U₁).isOpen
    intro z hz
    exact hv₁ (some ⟨z,hz⟩)
  let Z : Set X := I.subschemeι '' (((I.subschemeι ⁻¹ᵁ U₁ : I.subscheme.Opens) : Set I.subscheme)ᶜ)
  have hZ : Z.Finite := hfin.image _
  let : Finite Z := hZ.to_subtype
  obtain ⟨v₂,hv₂⟩ := exists_section_avoiding k s hs (fun z : Option Z => z.elim x Subtype.val)
  refine ⟨![v₀,v₁,v₂], ?_, ?_⟩
  swap
  · intro i
    fin_cases i
    · exact hv₀ ()
    · exact hv₁ none
    · exact hv₂ none
  apply top_unique
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
  exact ⟨2,hv₂ (some ⟨y,hyZ⟩)⟩

theorem surface_finite_projection_through [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p] [SmoothOfRelativeDimension 2 p]
    (L : LineBundle X) (s : σ → (O X ⟶ L.sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)] :
    ∀ x : X, ∃ t : Fin 3 → (O X ⟶ L.sheaf), ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
      IsFinite (sectionsMorphism
        (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) ∧ ∀ i, x ∈ SectionOpens.isoOpen (t i) := by
  intro x
  let k := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨v,hv,hx⟩ := surface_three_sections_through p L s hs x
  let t : Fin 3 → (O X ⟶ L.sheaf) := fun i => sectionCombination k s (v i)
  have ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤ := hv
  refine ⟨t,ht,?_,hx⟩
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

end


end OAI
