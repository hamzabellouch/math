import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularPairExtObstruction

namespace OAI

noncomputable section
universe u
open IsLocalRing RingTheory.Sequence
namespace PiExponentSiegel.W58

section Flat
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem weaklyRegular_map_of_flat [Module.Flat R S] (rs : List R)
    (h : IsWeaklyRegular R rs) :
    IsWeaklyRegular S (rs.map (algebraMap R S)) := by
  apply (isWeaklyRegular_map_algebraMap_iff S S rs).mpr
  exact ((TensorProduct.rid R S).isWeaklyRegular_congr rs).mp
    (h.isWeaklyRegular_lTensor (M₂ := S))

theorem regular_map_of_flat_of_mem_maximalIdeal [Module.Flat R S]
    [IsLocalRing S] (rs : List R) (h : IsRegular R rs)
    (hm : ∀ r ∈ rs, algebraMap R S r ∈ maximalIdeal S) :
    IsRegular S (rs.map (algebraMap R S)) := by
  apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (M := S) (rs := rs.map (algebraMap R S)) ?_).mpr
  · exact weaklyRegular_map_of_flat rs h.toIsWeaklyRegular
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact hm r hr

end Flat

section LocalQuotient
variable {R : Type*} [CommRing R]
variable (L : Type*) [CommRing L] [Algebra R L]
variable (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime L P] [IsLocalRing L]

omit [IsLocalRing L] in
theorem localized_ideal_eq_map (I : Ideal R) :
    I.localized' L P.primeCompl (Algebra.linearMap R L) =
      I.map (algebraMap R L) := by
  rw [Submodule.localized'_eq_span]
  rfl

def localizedIdealQuotientEquiv (I : Ideal R) :
    (L ⧸ I.localized' L P.primeCompl (Algebra.linearMap R L)) ≃ₗ[L]
      L ⧸ I.map (algebraMap R L) :=
  Submodule.quotEquivOfEq _ _ (localized_ideal_eq_map L P I)

theorem associatedPrime_quotient_atPrime (I : Ideal R)
    (hP : IsAssociatedPrime P (R ⧸ I)) :
    IsAssociatedPrime (maximalIdeal L) (L ⧸ I.map (algebraMap R L)) := by
  apply (localizedIdealQuotientEquiv L P I).isAssociatedPrime_iff.mp
  apply Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      P.primeCompl (I.toLocalizedQuotient' L P.primeCompl (Algebra.linearMap R L))
  change IsAssociatedPrime ((maximalIdeal L).under R) (R ⧸ I)
  rwa [IsLocalization.AtPrime.under_maximalIdeal L P]

omit [P.IsPrime] in
theorem ideal_le_of_quotient_associatedPrime (I : Ideal R)
    (hP : IsAssociatedPrime P (R ⧸ I)) : I ≤ P := by
  simpa only [Submodule.annihilator_top, Ideal.annihilator_quotient] using
    hP.annihilator_le

theorem regular_list_at_associatedPrime
    (rs : List R) (hreg : IsRegular R rs)
    (hP : IsAssociatedPrime P (R ⧸ Ideal.ofList rs)) :
    IsRegular L (rs.map (algebraMap R L)) := by
  let : Module.Flat R L := IsLocalization.flat L P.primeCompl
  apply regular_map_of_flat_of_mem_maximalIdeal rs hreg
  intro r hr
  have hmem := ideal_le_of_quotient_associatedPrime P (Ideal.ofList rs) hP
    (Ideal.subset_span hr)
  change r ∈ (maximalIdeal L).under R
  rwa [IsLocalization.AtPrime.under_maximalIdeal L P]

end LocalQuotient

variable {R : Type u} [CommRing R]
variable (L : Type u) [CommRing L] [Algebra R L] [IsNoetherianRing L]
variable (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime L P]
variable [IsLocalRing L]

theorem regular_pair_localized_ext_obstruction (f g : R)
    (hreg : IsRegular R [f, g])
    (hP : IsAssociatedPrime P (R ⧸ Ideal.ofList [f, g])) :
    ∃ i : ℕ, i ≤ 2 ∧ ¬ Subsingleton
      (CategoryTheory.Abelian.Ext
        (ModuleCat.of L (L ⧸ maximalIdeal L)) (ModuleCat.of L L) i) := by
  have hr := regular_list_at_associatedPrime L P [f, g] hreg hP
  have ha := associatedPrime_quotient_atPrime L P (Ideal.ofList [f, g]) hP
  rw [Ideal.map_ofList] at ha
  simp only [List.map_cons, List.map_nil] at hr ha
  exact PiExponentJets.W18.regular_pair_associatedPrime_ext_obstruction
    (algebraMap R L f) (algebraMap R L g) hr (maximalIdeal L) ha

end PiExponentSiegel.W58

end

end OAI
