import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import OAI.NumberTheory.PiExponent.Geometry.ConePrimeProperties
import OAI.NumberTheory.PiExponent.LocalAlgebra.ConeRegularSequence
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalLength
import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedRadical
import OAI.NumberTheory.PiExponent.Polynomials.HomogeneousListHistory

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
open PiExponentSiegel.W17.ConeLocalLength
open scoped BigOperators Classical

theorem span_range_list_get {R : Type*} [CommSemiring R] (gs : List R) :
    Ideal.span (Set.range gs.get) = Ideal.ofList gs := by
  congr 1
  ext x
  exact List.mem_iff_get.symm

theorem span_range_map_list_get {R S : Type*} [CommSemiring S]
    (gs : List R) (f : R → S) :
    Ideal.span (Set.range (fun i => f (gs.get i))) = Ideal.ofList (gs.map f) := by
  congr 1
  ext x
  change (∃ i, f (gs.get i) = x) ↔ x ∈ gs.map f
  constructor
  · rintro ⟨i,rfl⟩
    exact List.mem_map.mpr ⟨gs.get i,List.mem_iff_get.mpr ⟨i,rfl⟩,rfl⟩
  · intro hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ha
    exact ⟨i,rfl⟩

theorem finiteLength_localized_minimal_quotient
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I P : Ideal R) [P.IsPrime] (hP : P ∈ I.minimalPrimes) :
    IsFiniteLength (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) := by
  let L := Localization.AtPrime P
  let J := I.map (algebraMap R L)
  have hrad : J.radical = IsLocalRing.maximalIdeal L :=
    localized_radical_eq_maximal_of_mem_minimalPrimes I P hP
  let : J.radical.IsPrime := by rw [hrad]; infer_instance
  have hmin : IsLocalRing.maximalIdeal L ∈ J.minimalPrimes := by
    rw [← hrad]
    exact radical_mem_minimalPrimes J
  let : IsArtinianRing (L ⧸ J) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing J hmin
  apply Module.length_ne_top_iff.mp
  rw [Module.length_eq_of_surjective (M := L ⧸ J)
    (show Function.Surjective (algebraMap L (L ⧸ J)) from Ideal.Quotient.mk_surjective)]
  exact Module.length_ne_top

theorem affine_local_regular_list_bezout
    {k : Type} [Field k] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (gs : List (MvPolynomial (Fin n) k)) (D : ℕ)
    (hdegree : ∀ g ∈ gs, g.totalDegree ≤ D)
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime P)
      (gs.map (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))))
    (hlen : gs.length ≤ n) (hP : P ∈ (Ideal.ofList gs).minimalPrimes) :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (Ideal.ofList gs).map
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))) ≤
      ((D ^ gs.length : ℕ) : ℕ∞) := by
  let hs := gs.map homogenize
  let degrees : Fin hs.length → ℕ := fun i =>
    (gs[i.val]'(by simpa only [hs,List.length_map] using i.isLt)).totalDegree
  have hhom : ∀ i : Fin hs.length, hs[i].IsHomogeneous (degrees i) := by
    intro i
    simpa only [hs, List.getElem_map, Fin.getElem_fin, degrees] using
      homogenize_isHomogeneous (gs[i.val]'(by simpa only [hs,List.length_map] using i.isLt))
  have hconeReg := homogenized_list_regular_at_cone k (Fin n) P gs hreg
  have hget : P ∈ (Ideal.span (Set.range gs.get)).minimalPrimes := by
    simpa only [span_range_list_get] using hP
  have hconeMin := conePrime_minimal_over_homogenized k (Fin n) P gs.get hget
  rw [span_range_map_list_get] at hconeMin
  have hconeLen : hs.length < Fintype.card (Option (Fin n)) := by
    simp only [hs,List.length_map,Fintype.card_option,Fintype.card_fin]
    omega
  have hbound := homogeneous_local_regular_bezout (conePrime k (Fin n) P) none
    (homogenizing_coordinate_not_mem_conePrime k (Fin n) P)
    hs degrees hhom hconeReg hconeLen hconeMin
  have hfinite := finiteLength_localized_minimal_quotient
    (Ideal.span (Set.range gs.get)) P hget
  have hlength := homogenized_cone_local_length_eq k (Fin n) P gs.get hfinite
  rw [span_range_list_get, span_range_map_list_get] at hlength
  have hprod : (∏ i ∈ Finset.range hs.length, degreeAt degrees i) ≤ D ^ gs.length := by
    calc
      _ ≤ ∏ _i ∈ Finset.range hs.length, D := by
        apply Finset.prod_le_prod
        intro i hi
        have hi' : i < hs.length := Finset.mem_range.mp hi
        simp only [degreeAt,dite_eq_left hi',degrees]
        exact hdegree _ (List.getElem_mem _)
      _ = D ^ gs.length := by simp only [Finset.prod_const,Finset.card_range,hs,List.length_map]
  calc
    _ = Module.length (Localization.AtPrime (conePrime k (Fin n) P))
      (Localization.AtPrime (conePrime k (Fin n) P) ⧸ (Ideal.ofList hs).map
        (algebraMap (MvPolynomial (Option (Fin n)) k)
          (Localization.AtPrime (conePrime k (Fin n) P)))) := hlength.symm
    _ ≤ ((∏ i ∈ Finset.range hs.length, degreeAt degrees i : ℕ) : ℕ∞) := hbound
    _ ≤ _ := by exact_mod_cast hprod

end PiExponentJets.W22

end OAI
