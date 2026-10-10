import Mathlib.Data.Fintype.EquivFin
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OAI.NumberTheory.SiegelZeros.Differentials.DerivativeGeneratorBridge
import OAI.NumberTheory.SiegelZeros.Hilbert.HomogeneousListHistory
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.ConeRegularSequence
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.LocalLength
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.ParameterIntegration
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.RegularParameterSelectionLemmas

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W22

def LocalIsolatedBezoutStatement (k : Type*) [Field k] [IsAlgClosed k] [CharZero k] : Prop :=
  ∀ (h D : ℕ), 1 ≤ h → h ≤ 4 → 1 ≤ D →
  ∀ (f : Fin h → MvPolynomial (Fin 4) k),
    (∀ i, (f i).totalDegree ≤ D) →
  ∀ (P : PrimeSpectrum (MvPolynomial (Fin 4) k)),
    P.asIdeal ∈ (Ideal.span (Set.range f)).minimalPrimes →
    P.asIdeal.height = h →
    Module.length (Localization.AtPrime P.asIdeal)
      (Localization.AtPrime P.asIdeal ⧸
        (Ideal.span (Set.range f)).map
          (algebraMap (MvPolynomial (Fin 4) k) (Localization.AtPrime P.asIdeal))) ≤ D ^ h

end WeightedTorusJets.W22

end

end SiegelZeros

section

namespace SiegelZeros.W20

variable {k J : Type*} [Field k] [Infinite k] [IsAlgClosed k] [CharZero k]

theorem local_length_le_of_local_isolated_bezout
    (hBezout : WeightedTorusJets.W22.LocalIsolatedBezoutStatement k)
    (f : J → MvPolynomial (Fin 4) k)
    (P : PrimeSpectrum (MvPolynomial (Fin 4) k))
    (h D : ℕ) (hh1 : 1 ≤ h) (hh4 : h ≤ 4) (hD : 1 ≤ D)
    (hdegree : ∀ j, (f j).totalDegree ≤ D)
    (hminimal : P.asIdeal ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (hheight : P.asIdeal.height = h) :
    Module.length (Localization.AtPrime P.asIdeal)
      (Localization.AtPrime P.asIdeal ⧸
        (Ideal.span (Set.range f)).map
          (algebraMap (MvPolynomial (Fin 4) k) (Localization.AtPrime P.asIdeal))) ≤ D ^ h := by
  classical
  have hgen := WeightedTorusJets.W22.localized_radical_eq_maximal_of_mem_minimalPrimes
    (Ideal.span (Set.range f)) P.asIdeal hminimal
  obtain ⟨t, hcard, hdeg, hle, _hrad, _hprimary, htminimal⟩ :=
    exists_exact_localized_polynomial_parameters f P.asIdeal h D hgen hheight hdegree
  let e : t ≃ Fin h := Finset.equivFinOfCardEq hcard
  let selected : Fin h → MvPolynomial (Fin 4) k := fun i => (e.symm i).val
  have hrange : Set.range selected = (t : Set (MvPolynomial (Fin 4) k)) := by
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).property
    · intro hp
      refine ⟨e ⟨p, hp⟩, ?_⟩
      simp only [selected, Equiv.symm_apply_apply]
  have hsdegree : ∀ i, (selected i).totalDegree ≤ D :=
    fun i => hdeg (e.symm i) (e.symm i).property
  have hsminimal : P.asIdeal ∈ (Ideal.span (Set.range selected)).minimalPrimes := by
    rw [hrange]
    exact htminimal
  have hbound := hBezout h D hh1 hh4 hD selected hsdegree P hsminimal hheight
  rw [hrange] at hbound
  exact WeightedTorusJets.W22.ideal_quotient_length_le_of_bound
    (Ideal.map_mono hle) hbound

end SiegelZeros.W20

end

section

noncomputable section
namespace SiegelZeros.W23
open SiegelZeros.W58

@[reducible] local instance bezoutLocalHasQuotient {K : Type*} [Field K]
    (P : Ideal (TorusRing K)) [P.IsPrime] :
    HasQuotient (Localization.AtPrime P) (Ideal (Localization.AtPrime P)) :=
  @Ideal.instHasQuotient (Localization.AtPrime P) inferInstance

section LengthTransport
variable {A B : Type*} [CommRing A] [CommRing B]

theorem quotient_length_eq_of_ringEquiv (e : A ≃+* B) (I : Ideal A) (J : Ideal B)
    (hJI : J = I.map e.toRingHom) :
    Module.length A (A ⧸ I) = Module.length B (B ⧸ J) := by
  let q : A ⧸ I ≃+* B ⧸ J := Ideal.quotientEquiv I J e hJI
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  let l : (A ⧸ I) →ₛₗ[e.toRingHom] (B ⧸ J) :=
    { toFun := q
      map_add' := q.map_add
      map_smul' := by
        intro r x
        simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
        change q (Ideal.Quotient.mk I r * x) = Ideal.Quotient.mk J (e r) * q x
        rw [map_mul]
        congr 1 }
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso
    (Submodule.orderIsoMapComapOfBijective l q.bijective)

end LengthTransport

section Torus
variable {K : Type*} [Field K]

def polynomialComponentPrime (P : Ideal (TorusRing K)) : Ideal (AmbientPolynomial K) :=
  P.comap (algebraMap (AmbientPolynomial K) (TorusRing K))

instance polynomialComponentPrime_isPrime (P : Ideal (TorusRing K)) [P.IsPrime] :
    (polynomialComponentPrime P).IsPrime := Ideal.IsPrime.comap _

theorem polynomialComponentPrime_mem_minimalPrimes (J : Ideal (AmbientPolynomial K))
    (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : P ∈ (J.map (algebraMap (AmbientPolynomial K) (TorusRing K))).minimalPrimes) :
    polynomialComponentPrime P ∈ J.minimalPrimes := by
  rw [IsLocalization.minimalPrimes_map (Submonoid.powers (coordinateProduct K))
    (TorusRing K) J] at hP
  exact hP

theorem polynomialComponentPrime_height (P : Ideal (TorusRing K)) :
    (polynomialComponentPrime P).height = P.height :=
  IsLocalization.height_under (Submonoid.powers (coordinateProduct K)) P

def polynomialTorusLocalEquiv (P : Ideal (TorusRing K)) [P.IsPrime] :
    Localization.AtPrime (polynomialComponentPrime P) ≃ₐ[AmbientPolynomial K]
      Localization.AtPrime P :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers (coordinateProduct K)) P

@[simp] theorem polynomialTorusLocalEquiv_algebraMap
    (P : Ideal (TorusRing K)) [P.IsPrime] (f : AmbientPolynomial K) :
    polynomialTorusLocalEquiv P
      (algebraMap (AmbientPolynomial K) (Localization.AtPrime (polynomialComponentPrime P)) f) =
      algebraMap (AmbientPolynomial K) (Localization.AtPrime P) f :=
  (polynomialTorusLocalEquiv P).commutes f

theorem torus_localized_ideal_eq_map_polynomial_localized
    (J : Ideal (AmbientPolynomial K)) (P : Ideal (TorusRing K)) [P.IsPrime] :
    (J.map (algebraMap (AmbientPolynomial K) (TorusRing K))).map
        (algebraMap (TorusRing K) (Localization.AtPrime P)) =
      (J.map (algebraMap (AmbientPolynomial K)
        (Localization.AtPrime (polynomialComponentPrime P)))).map
        (polynomialTorusLocalEquiv P).toRingEquiv.toRingHom := by
  have he : (polynomialTorusLocalEquiv P).toRingEquiv.toRingHom.comp
      (algebraMap (AmbientPolynomial K) (Localization.AtPrime (polynomialComponentPrime P))) =
      algebraMap (AmbientPolynomial K) (Localization.AtPrime P) := by
    apply RingHom.ext
    intro f
    exact polynomialTorusLocalEquiv_algebraMap P f
  rw [Ideal.map_map, Ideal.map_map, he,
    ← IsScalarTower.algebraMap_eq (AmbientPolynomial K) (TorusRing K) (Localization.AtPrime P)]

def polynomialTorusLocalQuotientEquiv (J : Ideal (AmbientPolynomial K))
    (P : Ideal (TorusRing K)) [P.IsPrime] :
    (Localization.AtPrime (polynomialComponentPrime P) ⧸
      J.map (algebraMap (AmbientPolynomial K)
        (Localization.AtPrime (polynomialComponentPrime P)))) ≃+*
    (Localization.AtPrime P ⧸
      (J.map (algebraMap (AmbientPolynomial K) (TorusRing K))).map
        (algebraMap (TorusRing K) (Localization.AtPrime P))) :=
  Ideal.quotientEquiv _ _ (polynomialTorusLocalEquiv P).toRingEquiv
    (torus_localized_ideal_eq_map_polynomial_localized J P)

theorem polynomial_torus_local_quotient_length_eq (J : Ideal (AmbientPolynomial K))
    (P : Ideal (TorusRing K)) [P.IsPrime] :
    Module.length (Localization.AtPrime (polynomialComponentPrime P))
      (Localization.AtPrime (polynomialComponentPrime P) ⧸
        J.map (algebraMap (AmbientPolynomial K)
          (Localization.AtPrime (polynomialComponentPrime P)))) =
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸
        (J.map (algebraMap (AmbientPolynomial K) (TorusRing K))).map
          (algebraMap (TorusRing K) (Localization.AtPrime P))) :=
  (quotient_module_length_eq_intrinsic
    (J.map (algebraMap (AmbientPolynomial K)
      (Localization.AtPrime (polynomialComponentPrime P))))).trans
    ((intrinsic_length_eq_of_ringEquiv (polynomialTorusLocalQuotientEquiv J P)).trans
      (quotient_module_length_eq_intrinsic
        ((J.map (algebraMap (AmbientPolynomial K) (TorusRing K))).map
          (algebraMap (TorusRing K) (Localization.AtPrime P)))).symm)

end Torus

section Bezout
variable {K ι : Type*} [Field K] [Infinite K] [IsAlgClosed K] [CharZero K]

theorem torus_local_length_le_of_local_isolated_bezout
    (hBezout : WeightedTorusJets.W22.LocalIsolatedBezoutStatement K)
    (f : ι → AmbientPolynomial K) (D h : ℕ)
    (hdegree : ∀ i, (f i).totalDegree ≤ D) (hD : 1 ≤ D)
    (hh1 : 1 ≤ h) (hh4 : h ≤ 4)
    (P : Ideal (TorusRing K)) [P.IsPrime]
    (hminimal : P ∈ ((Ideal.span (Set.range f)).map
      (algebraMap (AmbientPolynomial K) (TorusRing K))).minimalPrimes)
    (hheight : P.height = h) :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ ((Ideal.span (Set.range f)).map
        (algebraMap (AmbientPolynomial K) (TorusRing K))).map
          (algebraMap (TorusRing K) (Localization.AtPrime P))) ≤ ((D ^ h : ℕ) : ℕ∞) := by
  have hbound := SiegelZeros.W20.local_length_le_of_local_isolated_bezout hBezout f
    (⟨polynomialComponentPrime P, inferInstance⟩ : PrimeSpectrum (AmbientPolynomial K))
    h D hh1 hh4 hD hdegree
    (polynomialComponentPrime_mem_minimalPrimes (Ideal.span (Set.range f)) P hminimal)
    ((polynomialComponentPrime_height P).trans hheight)
  rw [polynomial_torus_local_quotient_length_eq] at hbound
  simpa only [Nat.cast_pow] using hbound

end Bezout
end SiegelZeros.W23

end

end

namespace SiegelZeros

section

namespace WeightedTorusJets.W22

open WeightedTorusJets.W64
open SiegelZeros.W17.ConeLocalLength
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

end WeightedTorusJets.W22

end

section

namespace WeightedTorusJets.W22

theorem localIsolatedBezout_of_actual_regular_selection
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] :
    LocalIsolatedBezoutStatement k := by
  intro h D _hhpos hhfour _hD f hf P hP hheight
  have hrad := localized_radical_eq_maximal_of_mem_minimalPrimes
    (Ideal.span (Set.range f)) P.asIdeal hP
  obtain ⟨cs, _hcslength, hgslen, hgsdegree, hgscontained, hgsreg, hgsrad⟩ :=
    SiegelZeros.W58.polynomialLocal_exists_degree_bounded_regular_parameters
      k 4 P.asIdeal f D h hf hheight hrad
  let gs := cs.map (Finsupp.linearCombination k f)
  have hlen : gs.length = h := hgslen
  have hgsmin : P.asIdeal ∈ (Ideal.ofList gs).minimalPrimes :=
    mem_minimalPrimes_of_localized_radical (Ideal.ofList gs) P.asIdeal hgsrad
  have hselected := affine_local_regular_list_bezout 4 P.asIdeal gs D
    hgsdegree hgsreg (hlen.le.trans hhfour) hgsmin
  have htransfer := ideal_quotient_length_le_of_bound
    (Ideal.map_mono hgscontained) hselected
  have hpow : ((D ^ gs.length : ℕ) : ℕ∞) = (D : ℕ∞) ^ h := by
    rw [hlen, Nat.cast_pow]
  exact htransfer.trans hpow.le

end WeightedTorusJets.W22

end

end SiegelZeros

end OAI
