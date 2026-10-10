import OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation
import OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections
import OAI.NumberTheory.PiExponent.Approximation.SectionOpens
import OAI.NumberTheory.PiExponent.Cohomology.NakaiCohomology
import OAI.NumberTheory.PiExponent.Cohomology.NakaiEulerGrowth

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

private lemma mono_iso_inv_comp {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (f : A ⟶ D) [Mono f] : Mono (e.inv ≫ f) := inferInstance

def cartierPowerMultiply (L : LineBundle X) (s : GlobalSections X L.sheaf) (n : ℕ) :
    modulePow X L.sheaf n ⟶ modulePow X L.sheaf (n+1) :=
  (moduleTensorUnit (modulePow X L.sheaf n)).inv ≫
    moduleTensorMap s (𝟙 (modulePow X L.sheaf n))

theorem cartierPowerMultiply_mono [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) (n : ℕ) :
    Mono (cartierPowerMultiply L s n) := by
  let := L.mono_section s hs
  have hm : Mono (moduleTensorMap s (𝟙 (modulePow X L.sheaf n))) :=
    moduleTensorMap_mono s (L.pow n)
  exact @mono_iso_inv_comp X.Modules _ _ _ _
    (moduleTensorUnit (modulePow X L.sheaf n)) _ hm

def cartierPowerQuotient (L : LineBundle X) (s : GlobalSections X L.sheaf) (n : ℕ) :
    X.Modules := cokernel (cartierPowerMultiply L s n)

def cartierPowerSequence (L : LineBundle X) (s : GlobalSections X L.sheaf) (n : ℕ) :
    ShortComplex X.Modules :=
  ShortComplex.mk (cartierPowerMultiply L s n) (cokernel.π _) (cokernel.condition _)

theorem cartierPowerSequence_shortExact [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) (n : ℕ) :
    (cartierPowerSequence L s n).ShortExact := by
  have := cartierPowerMultiply_mono L s hs n
  change (ShortComplex.mk (cartierPowerMultiply L s n) (cokernel.π _)
    (cokernel.condition _)).ShortExact
  exact { exact := ShortComplex.exact_cokernel _ }

theorem cartierPowerMultiply_restrict_isIso (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (n : ℕ) (U : X.Opens)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (cartierPowerMultiply L s n)) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  have h : IsIso (R.map (moduleTensorMap s (𝟙 (modulePow X L.sheaf n)))) := by
    apply (isIso_comp_right_iff _ (moduleTensorRestrict U L.sheaf _).hom).mp
    rw [moduleTensorRestrict_natural]
    infer_instance
  change IsIso (R.map ((moduleTensorUnit _).inv ≫ moduleTensorMap s (𝟙 _)))
  rw [Functor.map_comp]
  infer_instance

theorem cartierPowerQuotient_restrict_isZero (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (n : ℕ) :
    IsZero ((cartierPowerQuotient L s n).restrict (sectionOpen X s).ι) := by
  let R := Scheme.Modules.restrictFunctor (sectionOpen X s).ι
  have : IsIso (R.map s) := PiExponentSeshadri.SectionOpens.isIso_restrict_isoOpen s
  have : IsIso (R.map (cartierPowerMultiply L s n)) :=
    cartierPowerMultiply_restrict_isIso L s n (sectionOpen X s)
  have hz : R.map (cokernel.π (cartierPowerMultiply L s n)) = 0 := by
    apply (cancel_epi (R.map (cartierPowerMultiply L s n))).mp
    rw [← R.map_comp, cokernel.condition, Functor.map_zero, comp_zero]
  have hπ : Epi (R.map (cokernel.π (cartierPowerMultiply L s n))) :=
    R.map_epi (cokernel.π (cartierPowerMultiply L s n))
  exact @IsZero.of_epi_eq_zero (sectionOpen X s).toScheme.Modules _ _ _ _
    (R.map (cokernel.π (cartierPowerMultiply L s n))) hπ hz

theorem eventual_cartierPower_sections_lift [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (hfinite : ∀ n,
      let _ := Module.compHom (cohomology (modulePow X L.sheaf n) 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology (modulePow X L.sheaf n) 1))
    (hzero : ∃ N, ∀ n, N ≤ n → ∀ z : cohomology (cartierPowerQuotient L s n) 1,
      z = 0) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (fun t : GlobalSections X (modulePow X L.sheaf (n+1)) =>
        t ≫ cokernel.π (cartierPowerMultiply L s n)) := by
  exact eventual_globalSections_surjective p (fun n => modulePow X L.sheaf n)
    (cartierPowerQuotient L s) (cartierPowerMultiply L s) (fun n => cokernel.π _)
    (fun n => cokernel.condition _) (fun n => cartierPowerSequence_shortExact L s hs n)
    hfinite hzero

end
end PiExponent.NumericalAmpleness

end OAI
