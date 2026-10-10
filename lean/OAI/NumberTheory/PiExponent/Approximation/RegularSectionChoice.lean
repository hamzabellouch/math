import OAI.NumberTheory.PiExponent.Approximation.RegularSectionMono
import OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections
import OAI.NumberTheory.PiExponent.Cohomology.CurveEuler
import OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct
import OAI.NumberTheory.PiExponent.LocalAlgebra.AssociatedPrimeAvoidance

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem finite_affine_frame_cover [CompactSpace X] (L : LineBundle X) :
    ∃ l : ℕ, ∃ U : Fin l → X.affineOpens,
      (⨆ i, (U i).1) = ⊤ ∧
      Nonempty (∀ i, L.sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme) := by
  classical
  have h (x : X) : ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) := by
    obtain ⟨U, hx, he, _⟩ := common_affine_frames L L x
    exact ⟨U, hx, he⟩
  choose U hx e using h
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((U x).1 : Set X)) (fun x => (U x).1.isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x,hx x⟩)
  let E := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, fun j => U (E j).val, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi,hx⟩ := Set.mem_iUnion.mp hi
    apply Opens.mem_iSup.mpr
    refine ⟨E.symm ⟨i,hi⟩,?_⟩
    change x ∈ (U (E (E.symm ⟨i,hi⟩)).val).1
    rw [Equiv.apply_symm_apply]
    exact hx
  · exact ⟨fun j => (e (E j).val).some⟩

theorem coefficients_span_top_of_section_cover (L : LineBundle X) {k : ℕ}
    (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ j, sectionOpen X (s j)) = ⊤)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span (Set.range (fun j => coefficient e (restrictSection U.1.ι (s j)))) = ⊤ := by
  have : IsAffine U.1.toScheme := U.2
  have hc : (⨆ j, U.1.toScheme.basicOpen (coefficient e (restrictSection U.1.ι (s j)))) = ⊤ := by
    exact (iSup_congr fun j => (preimage_isoOpen (s j) U.1.ι e).symm).trans
      (U.1.ι.iSup_preimage_eq_top hs)
  apply (isAffineOpen_top U.1.toScheme).iSup_basicOpen_eq_self_iff.mp
  apply top_unique
  intro x _
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ j,
    U.1.toScheme.basicOpen (coefficient e (restrictSection U.1.ι (s j))) by rw [hc]; trivial)
  exact Opens.mem_iSup.mpr ⟨⟨_, Set.mem_range_self j⟩, hj⟩

def localCoefficientAddHom (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) :
    GlobalSections X L.sheaf →+ Γ(U.toScheme, ⊤) where
  toFun s := coefficient e (restrictSection U.ι s)
  map_zero' := by
    exact (congrArg (coefficient e) (restrictSection_zero U.ι)).trans (coefficient_zero e)
  map_add' s t := by
    simp only [coefficient, restrictSection]
    erw [(Scheme.Modules.restrictFunctor U.ι).map_add (f := s) (g := t),
      Preadditive.comp_add, Preadditive.add_comp]
    rfl

private theorem iso_inv_map_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B : C} {T : D} (e : F.obj A ≅ T) (f : A ⟶ A) (s : A ⟶ B) :
    e.inv ≫ F.map (f ≫ s) = ((e.inv ≫ F.map f) ≫ e.hom) ≫ e.inv ≫ F.map s := by
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

theorem localCoefficient_scalar (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme)
    (r : Γ(X, ⊤)) (s : GlobalSections X L.sheaf) :
    coefficient e (restrictSection U.ι (scalarEnd r ≫ s)) =
      U.ι.appTop r * coefficient e (restrictSection U.ι s) := by
  have hscalar : restrictSection U.ι (scalarEnd r) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom = scalarEnd (U.ι.appTop r) := by
    apply endValue_injective
    erw [endValue_restrict U.ι (scalarEnd r), endValue_scalarEnd, endValue_scalarEnd]
  have hrestrict : restrictSection U.ι (scalarEnd r ≫ s) =
      scalarEnd (U.ι.appTop r) ≫ restrictSection U.ι s := by
    rw [← hscalar]
    exact iso_inv_map_comp (Scheme.Modules.restrictFunctor U.ι)
      (Scheme.Modules.restrictUnitIso U.ι) (scalarEnd r) s
  rw [hrestrict]
  change endValue (scalarEnd (U.ι.appTop r) ≫ restrictSection U.ι s ≫ e.hom) = _
  rw [endValue_comp, endValue_scalarEnd]
  rfl

def sectionLinearCombination (L : LineBundle X) {k : ℕ}
    (a : ℂ →+* Γ(X, ⊤)) (s : Fin k → GlobalSections X L.sheaf) (c : Fin k → ℂ) :
    GlobalSections X L.sheaf := ∑ j, scalarEnd (a (c j)) ≫ s j

theorem localCoefficient_linearCombination (L : LineBundle X) {k : ℕ}
    (a : ℂ →+* Γ(X, ⊤)) (s : Fin k → GlobalSections X L.sheaf) (c : Fin k → ℂ)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ O U.toScheme) :
    coefficient e (restrictSection U.ι (sectionLinearCombination L a s c)) =
      ∑ j, U.ι.appTop (a (c j)) * coefficient e (restrictSection U.ι (s j)) := by
  change localCoefficientAddHom L U e (∑ j, scalarEnd (a (c j)) ≫ s j) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact localCoefficient_scalar L U e _ _

theorem exists_mono_linearCombination_of_finite_cover [IsNoetherian X]
    (L : LineBundle X) {k : ℕ} (a : ℂ →+* Γ(X, ⊤))
    (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ j, sectionOpen X (s j)) = ⊤) :
    ∃ c : Fin k → ℂ, Mono (sectionLinearCombination L a s c) := by
  classical
  obtain ⟨l, U, hU, ⟨e⟩⟩ := finite_affine_frame_cover L
  let R (i : Fin l) : Type := Γ((U i).1.toScheme, ⊤)
  have hAff (i : Fin l) : IsAffine (U i).1.toScheme := (U i).2
  let alg (i : Fin l) : Algebra ℂ (R i) := ((U i).1.ι.appTop.hom.comp a).toAlgebra
  let (i : Fin l) : Algebra ℂ (R i) := alg i
  have hNoeth (i : Fin l) : IsNoetherianRing (R i) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (U i).1.toScheme⟩
  let b (i : Fin l) (j : Fin k) : R i := coefficient (e i) (restrictSection (U i).1.ι (s j))
  have hb (i : Fin l) : Ideal.span (Set.range (b i)) = ⊤ :=
    coefficients_span_top_of_section_cover L s hs (U i) (e i)
  obtain ⟨c, hc⟩ := GeometrySupport.AssociatedPrimeAvoidance.exists_regular_combination (K := ℂ) (ι := Fin l) (J := Fin k) R b hb
  refine ⟨c, section_mono_of_regular_affine_frames L _ ?_⟩
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, (U i).1 by rw [hU]; trivial)
  refine ⟨U i, hi, e i, ?_⟩
  rw [localCoefficient_linearCombination]
  simpa only [R, b, Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.comp_apply] using hc i

theorem exists_mono_section_of_finite_cover [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) {k : ℕ}
    (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ j, sectionOpen X (s j)) = ⊤) :
    ∃ t : GlobalSections X L.sheaf, Mono t := by
  obtain ⟨c, hc⟩ := exists_mono_linearCombination_of_finite_cover L (baseScalars p) s hs
  exact ⟨sectionLinearCombination L (baseScalars p) s c, hc⟩

end
end PiExponent.NumericalAmpleness

end OAI
