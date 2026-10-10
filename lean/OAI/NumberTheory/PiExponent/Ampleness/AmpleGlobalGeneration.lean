import OAI.NumberTheory.PiExponent.Ampleness.AmpleCommonDegree
import OAI.NumberTheory.PiExponent.Approximation.GlueGlobalGenerators
import OAI.NumberTheory.PiExponent.Approximation.TwistGlobalExtension
import OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation

namespace OAI

namespace PiExponent.AmpleGlobalGeneration
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CoherentAffineFinite
variable {X : Scheme.{0}}

theorem sectionMultiply_isIso_restrict (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) (U : X.Opens)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (moduleSectionMultiplyRight M s)) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  have h : IsIso (R.map (moduleTensorMap (𝟙 M) s)) := by
    apply (isIso_comp_right_iff _ (moduleTensorRestrict U M L).hom).mp
    rw [moduleTensorRestrict_natural]
    infer_instance
  change IsIso (R.map ((moduleTensorRightUnit M).inv ≫ moduleTensorMap (𝟙 M) s))
  rw [Functor.map_comp]
  infer_instance

theorem twistSection_isIso_restrict (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (sectionOpen X s).ι).map
      ((moduleTwistSection L s n).app M)) := by
  have : IsIso ((Scheme.Modules.restrictFunctor (sectionOpen X s).ι).map s) :=
    PiExponentSeshadri.SectionOpens.isIso_restrict_isoOpen s
  induction n with
  | zero => change IsIso ((Scheme.Modules.restrictFunctor (sectionOpen X s).ι).map (𝟙 M)); infer_instance
  | succ n ih =>
    change IsIso ((Scheme.Modules.restrictFunctor (sectionOpen X s).ι).map
      (((moduleTwistSection L s n).app M) ≫
        moduleSectionMultiplyRight ((moduleTwistFunctor L n).obj M) s))
    rw [Functor.map_comp]
    have := sectionMultiply_isIso_restrict ((moduleTwistFunctor L n).obj M) s (sectionOpen X s)
    infer_instance

lemma openSectionEquiv_restrict_from_top (M : X.Modules) (U : X.Opens)
    (z : Γ(M,⊤)) :
    openSectionEquiv M U (restrictSection U.ι ((moduleSectionEquiv M).symm z)) =
      M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op z := by
  rw [openSectionEquiv_restrict]
  have h := section_value_natural ((moduleSectionEquiv M).symm z)
    (homOfLE (show U ≤ ⊤ from le_top))
  rw [← moduleSectionEquiv_apply, Equiv.apply_symm_apply] at h
  exact h.symm

lemma openSectionEquiv_postcomp {M N : X.Modules} (f : M ⟶ N) (U : X.Opens)
    (a : structureSheaf U.toScheme ⟶ M.restrict U.ι) :
    openSectionEquiv N U (a ≫ (Scheme.Modules.restrictFunctor U.ι).map f) =
      f.app U (openSectionEquiv M U a) := by
  change N.presheaf.map (eqToHom U.ι_image_top.symm).op
    (f.app (U.ι ''ᵁ ⊤) (a.app ⊤ (1 : Γ(U.toScheme,⊤)))) =
    f.app U (M.presheaf.map (eqToHom U.ι_image_top.symm).op
      (a.app ⊤ (1 : Γ(U.toScheme,⊤))))
  exact (congr($(f.mapPresheaf.naturality (eqToHom U.ι_image_top.symm).op)
    (a.app ⊤ (1 : Γ(U.toScheme,⊤))))).symm

theorem affine_local_generators (M : X.Modules) [M.IsFinitePresentation]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ σ : (M.restrict U.ι).GeneratingSections, σ.IsFiniteType := by
  have : IsAffine U.toScheme := hU
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  have := affine_sections_finite_of_localGenerators (M.restrict U.ι)
    ((locallyFinitelyGenerated_of_finitePresentation M).restrict U.ι)
  exact affine_exists_finite_generators (M.restrict U.ι)

theorem eventual_global_generators_of_section_cover [NoetherianSpace X]
    (L : LineBundle X) (M : X.Modules) [M.IsFinitePresentation]
    {ι : Type} [Finite ι] (s : ι → (structureSheaf X ⟶ L.sheaf))
    (hcover : (⨆ i, sectionOpen X (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (sectionOpen X (s i))) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : ((moduleTwistFunctor L n).obj M).GeneratingSections, G.IsFiniteType := by
  classical
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  let U (i : ι) := sectionOpen X (s i)
  choose σ hσ using fun i => affine_local_generators M (U i) (haffine i)
  let (i : ι) : (σ i).IsFiniteType := hσ i
  let (i : ι) : Finite (σ i).I := (hσ i).finite
  let a (i : ι) (j : (σ i).I) :=
    (M.restrict (U i).ι).unitHomEquiv.symm ((σ i).s j)
  let x (i : ι) (j : (σ i).I) : Γ(M,U i) := openSectionEquiv M (U i) (a i j)
  choose d hd using fun ij : Σ i, (σ i).I =>
    PiExponent.TwistGlobalExtension.global_twist_extension_native L (s ij.1) M (x ij.1 ij.2)
  let : Fintype (Σ i, (σ i).I) := Fintype.ofFinite _
  let N := Finset.univ.sup d
  refine ⟨N, fun n hn => ?_⟩
  let Q := (moduleTwistFunctor L n).obj M
  have hn' (ij : Σ i, (σ i).I) : d ij ≤ n :=
    (Finset.le_sup (f := d) (Finset.mem_univ ij)).trans hn
  choose z hz using fun ij : Σ i, (σ i).I => hd ij n (hn' ij)
  let f (i : ι) : M.restrict (U i).ι ⟶ Q.restrict (U i).ι :=
    (Scheme.Modules.restrictFunctor (U i).ι).map ((moduleTwistSection L (s i) n).app M)
  have hf (i : ι) : IsIso (f i) := twistSection_isIso_restrict L (s i) M n
  let τ (i : ι) : (Q.restrict (U i).ι).GeneratingSections :=
    SheafOfModules.GeneratingSections.equivOfIso
      (@asIso _ _ _ _ (f i) (hf i)) (σ i)
  let (i : ι) : (τ i).IsFiniteType := ⟨(hσ i).finite⟩
  let t (i : ι) (j : (τ i).I) : GlobalSections X Q :=
    (moduleSectionEquiv Q).symm (z ⟨i,j⟩)
  have ht (i : ι) (j : (τ i).I) : restrictSection (U i).ι (t i j) =
      (Q.restrict (U i).ι).unitHomEquiv.symm ((τ i).s j) := by
    apply (openSectionEquiv Q (U i)).injective
    change openSectionEquiv Q (U i)
      (restrictSection (U i).ι ((moduleSectionEquiv Q).symm (z ⟨i,j⟩))) =
      openSectionEquiv Q (U i) ((Q.restrict (U i).ι).unitHomEquiv.symm
        (SheafOfModules.sectionsMap (f i) ((σ i).s j)))
    erw [openSectionEquiv_restrict_from_top, ← SheafOfModules.unitHomEquiv_symm_comp]
    erw [openSectionEquiv_postcomp]
    exact hz ⟨i,j⟩
  exact PiExponent.GlueGlobalGenerators.exists_finite_global_generators Q U hcover τ t ht

theorem ample_power_eventual_global_generators [NoetherianSpace X]
    (L : LineBundle X) (hL : L.IsAmple) (M : X.Modules) [M.IsFinitePresentation] :
    ∃ d : ℕ, 0 < d ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : ((moduleTwistFunctor (L.pow d) n).obj M).GeneratingSections, G.IsFiniteType := by
  obtain ⟨d, hd, l, s, hcover, haffine, _⟩ := L.ample_common_degree_cover hL
  exact ⟨d, hd, eventual_global_generators_of_section_cover (L.pow d) M s hcover haffine⟩

end
end PiExponent.AmpleGlobalGeneration

end OAI
