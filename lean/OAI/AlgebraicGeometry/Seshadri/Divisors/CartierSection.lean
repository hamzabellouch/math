import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.Sections
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionIdeal

namespace OAI

section
noncomputable section
                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames
variable {X Y : Scheme}

lemma LineBundle.restrict_sections_injective [IsIntegral X] (L : LineBundle X)
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y] :
    Function.Injective (fun s : GlobalSections X L.sheaf =>
      (Scheme.Modules.restrictFunctor f).map s) := by
  intro s t h
  let U : X.Opens := f ''ᵁ ⊤
  have : Nonempty U := by
    obtain ⟨y⟩ := ‹Nonempty Y›
    exact ⟨⟨f y, y, Set.mem_univ y, rfl⟩⟩
  apply L.section_restriction_injective U
  have he := congrArg (fun s : (structureSheaf X).restrict f ⟶ L.sheaf.restrict f =>
    s.app ⊤ (1 : Γ(X, U))) h
  exact he

lemma LineBundle.restricted_coefficient_injective [IsIntegral X] (L : LineBundle X)
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y]
    (e : L.sheaf.restrict f ≅ O Y) :
    Function.Injective (fun s : GlobalSections X L.sheaf => coefficient e (restrictSection f s)) := by
  intro s t h
  apply L.restrict_sections_injective f
  let u : (structureSheaf X).restrict f ≅ structureSheaf Y :=
    Scheme.Modules.restrictUnitIso f
  apply (cancel_epi u.inv).mp
  exact coefficient_injective e h

lemma LineBundle.section_coefficient_regular [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (U : X.affineOpens) [Nonempty U.1]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    IsRegular (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))) := by
  apply isRegular_iff_ne_zero.mpr
  intro h
  apply hs
  apply L.restricted_coefficient_injective U.1.ι e
  have he := (ConcreteCategory.bijective_of_isIso U.1.topIso.hom).injective
  apply he
  change U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) =
    U.1.topIso.hom (coefficient e (restrictSection U.1.ι (0 : O X ⟶ L.sheaf)))
  exact h.trans (by rw [restrictSection_zero, coefficient_zero, map_zero])
end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

theorem sectionIdeal_effective_cartier [IsIntegral X] (L : LineBundle X)
    (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ L.sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → K)
    (hv : sectionCombination k s v ≠ 0) :
    InvertiblePullbackIdeal (sectionIdeal k s hs v) (𝟙 X) := by
  apply MaximalSeshadri.InvertibleLocal.invertible_of_affine_equations
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hs.ge (Set.mem_univ x))
  obtain ⟨_, ⟨U,hUa,rfl⟩,hxU,hU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hi (SectionOpens.isoOpen (s i)).isOpen
  let A : X.affineOpens := ⟨U,hUa⟩
  let : Nonempty U := ⟨⟨x,hxU⟩⟩
  let e := sectionFrameOn (s i) U hU
  exact ⟨A,hxU,_,L.section_coefficient_regular _ hv A e,
    sectionIdeal_on k s hs v A i hU⟩

lemma idealSheaf_mem_support_of_prime (J : X.IdealSheafData)
    (U : X.affineOpens) (p : X) (hpU : p ∈ U.1)
    (hJ : J.ideal U ≤ (U.2.isoSpec.hom ⟨p,hpU⟩).asIdeal) : p ∈ J.support := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hpU]
  have hmem : U.2.isoSpec.hom ⟨p,hpU⟩ ∈ PrimeSpectrum.zeroLocus (J.ideal U) := hJ
  rw [← U.2.fromSpec_preimage_zeroLocus] at hmem
  have he : U.2.fromSpec (U.2.isoSpec.hom ⟨p,hpU⟩) = p := by
    change (U.2.isoSpec.hom ≫ U.2.fromSpec) ⟨p,hpU⟩ = p
    rw [U.2.isoSpec_hom_fromSpec]
    rfl
  change U.2.fromSpec (U.2.isoSpec.hom ⟨p,hpU⟩) ∈ X.zeroLocus (U := U.1) (J.ideal U) at hmem
  rwa [he] at hmem
end
end MaximalSeshadri.Projective
end

section

end


end
end

end OAI
