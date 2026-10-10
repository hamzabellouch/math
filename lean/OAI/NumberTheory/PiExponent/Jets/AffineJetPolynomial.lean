import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChartRestriction
import OAI.NumberTheory.PiExponent.Jets.AffineJetQuotient

namespace OAI

noncomputable section
namespace PiExponent.AffineJetPolynomial
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.BlowupJetSurjectivity PiExponent.AffineJetSupport PiExponent.AffineJetQuotient
open PiExponent.ExceptionalAffineChart
open PiExponentSeshadri.IdealPullback
variable {X : Scheme} {R : Type} [CommRing R]

theorem map_ideal_functionsOnOpenEquiv (I : X.IdealSheafData)
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (J : Ideal R) (hJ : I.comap j = specIdeal J) :
    (I.ideal (chartOpen j)).map (functionsOnOpenEquiv j).toRingHom = J := by
  let : IsAffine j.opensRange.toScheme := isAffineOpen_opensRange j
  change (I.ideal (chartOpen j)).map
    ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp
      (j.isoOpensRange.hom.appTop.hom.comp (chartOpen j).1.topIso.inv.hom)) = J
  dsimp +instances only [chartOpen]
  rw [← Ideal.map_map, ← Ideal.map_map]
  erw [← comap_ι_top I (chartOpen j)]
  erw [← comap_top (I.comap j.opensRange.ι) j.isoOpensRange.hom]
  rw [← Scheme.IdealSheafData.comap_comp]
  change ((I.comap (j.isoOpensRange.hom ≫ j.opensRange.ι)).ideal
    ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom = J
  rw [j.isoOpensRange_hom_ι, hJ, specIdeal_top, Ideal.map_map]
  have he : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom = RingHom.id _ := by
    apply RingHom.ext
    intro r
    exact (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id_apply r
  rw [he, Ideal.map_id]

def polynomialCoefficient (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (A : LineBundle X) (n : ℕ)
    (e : A.sheaf.restrict (chartOpen j).1.ι ≅ structureSheaf (chartOpen j).1.toScheme)
    (s : GlobalSections X (modulePow X A.sheaf n)) : R :=
  functionsOnOpenEquiv j (globalSectionCoefficient A n (chartOpen j) e s)

theorem polynomialQuotient_surjective_of_jetRestriction
    (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (e : A.sheaf.restrict (chartOpen j).1.ι ≅ structureSheaf (chartOpen j).1.toScheme)
    (J : Ideal R) (hJ : I.comap j = specIdeal J)
    (hs : ((I^n).support : Set X) ⊆ j.opensRange)
    (hjet : Function.Surjective (jetRestriction I A n)) :
    Function.Surjective (fun s : GlobalSections X (modulePow X A.sheaf n) =>
      Ideal.Quotient.mk (J^n) (polynomialCoefficient j A n e s)) := by
  have hpow : (I^n).comap j = specIdeal (J^n) := by
    rw [comap_pow, hJ, specIdeal_pow]
  have hmap := map_ideal_functionsOnOpenEquiv (I^n) j (J^n) hpow
  have hsource := coefficient_quotient_surjective_of_jetRestriction I A n (chartOpen j) e hs hjet
  intro q
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨s, hs⟩ := hsource (Ideal.Quotient.mk ((I^n).ideal (chartOpen j))
    ((functionsOnOpenEquiv j).symm P))
  refine ⟨s, Ideal.Quotient.eq.mpr ?_⟩
  have hs' := (Ideal.Quotient.eq (R := Γ(X,(chartOpen j).1))
    (I := (I^n).ideal (chartOpen j))).mp hs
  have hm := Ideal.mem_map_of_mem (functionsOnOpenEquiv j).toRingHom hs'
  erw [hmap] at hm
  let c : Γ(X,j.opensRange) := globalSectionCoefficient A n (chartOpen j) e s
  change (functionsOnOpenEquiv j) (c - (functionsOnOpenEquiv j).symm P) ∈ J^n at hm
  rw [(functionsOnOpenEquiv j).map_sub] at hm
  simpa only [RingEquiv.apply_symm_apply, polynomialCoefficient, c] using hm

end PiExponent.AffineJetPolynomial
end

end OAI
