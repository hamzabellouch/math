import OAI.NumberTheory.PiExponent.Geometry.SectionCartierRegular

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X Y : Scheme.{0}}

theorem pullbackSection_surjective_of_unit_surjective (f : Y ⟶ X) (L : LineBundle X)
    (h : Function.Surjective (fun s : GlobalSections X L.sheaf =>
      s ≫ PiExponentSeshadri.LineClosedUnit.map f L)) :
    Function.Surjective (fun s : GlobalSections X L.sheaf => pullbackSection f s) := by
  intro σ
  let A := Scheme.Modules.pullbackPushforwardAdjunction f
  let e := A.homEquiv (structureSheaf X) ((Scheme.Modules.pullback f).obj L.sheaf)
  obtain ⟨s,hs⟩ := h (e ((pullbackUnitIso f).hom ≫ σ))
  have he : (Scheme.Modules.pullback f).map s = (pullbackUnitIso f).hom ≫ σ := by
    apply e.injective
    have hn := A.homEquiv_naturality_left s (𝟙 ((Scheme.Modules.pullback f).obj L.sheaf))
    simpa only [e, Category.comp_id, Adjunction.homEquiv_unit, Functor.map_id,
      Category.comp_id] using! hn.trans hs
  refine ⟨s,?_⟩
  change (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s = σ
  exact (congrArg (fun t : (Scheme.Modules.pullback f).obj (structureSheaf X) ⟶
      (Scheme.Modules.pullback f).obj L.sheaf => (pullbackUnitIso f).inv ≫ t) he).trans
    ((pullbackUnitIso f).inv_hom_id_assoc σ)

theorem eventual_cartier_restriction_section_lifting
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s]
    (hfinite : ∀ n, letI := Module.compHom (cohomology (L.pow n).sheaf 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology (L.pow n).sheaf 1))
    (hzero : ∃ N, ∀ n, N ≤ n → ∀ z :
      cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf) 1,
      z = 0) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (fun t : GlobalSections X (L.pow (n+1)).sheaf =>
        pullbackSection (zeroIdeal L s).subschemeι t) := by
  let i := (zeroIdeal L s).subschemeι
  let F : ℕ → X.Modules := fun n => (L.pow n).sheaf
  let Q : ℕ → X.Modules := fun n => (Scheme.Modules.pushforward i).obj
    ((Scheme.Modules.pullback i).obj (L.pow (n+1)).sheaf)
  let f : ∀ n, F n ⟶ F (n+1) := fun n => cartierPowerMultiply L s n
  let g : ∀ n, F (n+1) ⟶ Q n := fun n => PiExponentSeshadri.LineClosedUnit.map i (L.pow (n+1))
  have hex := fun n => regular_cartierPower_restriction_shortExact p L s n
  let hz : ∀ n, f n ≫ g n = 0 := fun n => (hex n).choose
  have hshort : ∀ n, (ShortComplex.mk (f n) (g n) (hz n)).ShortExact :=
    fun n => (hex n).choose_spec
  have hzero' : ∃ N, ∀ n, N ≤ n → ∀ z : cohomology (Q n) 1, z = 0 := by
    obtain ⟨N,hN⟩ := hzero
    refine ⟨N,fun n hn z => ?_⟩
    let e := ClosedImmersionSerreTransfer.cohomologyLinearEquiv i p
      ((Scheme.Modules.pullback i).obj (L.pow (n+1)).sheaf) 1
    obtain ⟨w,rfl⟩ := e.surjective z
    rw [hN n hn w,map_zero]
  obtain ⟨N,hN⟩ := eventual_globalSections_surjective p F Q f g hz hshort hfinite hzero'
  refine ⟨N,fun n hn => ?_⟩
  exact pullbackSection_surjective_of_unit_surjective i (L.pow (n+1)) (hN n hn)

end
end PiExponent.NumericalAmpleness

end OAI
