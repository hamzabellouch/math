import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.PolynomialBox
import OAI.NumberTheory.SiegelZeros.Structure.Homogenize

namespace OAI

namespace SiegelZeros

open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
open scoped BigOperators
open scoped BigOperators
open MvPolynomial
namespace WeightedTorusJets.Geometry

open scoped AlgebraMonoidAlgebra

attribute [local instance] MvPolynomial.algebraMvPolynomial

noncomputable def coordinateLocalizedPrime {K σ : Type*} [Field K]
    (s : Set σ) (p : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial (sᶜ : Set σ) (FractionRing (MvPolynomial s K))) :=
  (p.comap (coordinateSplit (K := K) s).symm.toRingHom).map
    (algebraMap (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K))
      (MvPolynomial (sᶜ : Set σ) (FractionRing (MvPolynomial s K))))

theorem coordinateLocalizedPrime_height {K σ : Type*} [Field K]
    (s : Set σ) (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (hs : AlgebraicIndependent K (fun i : s =>
      algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
        (Ideal.Quotient.mk p (MvPolynomial.X i)))) :
    (coordinateLocalizedPrime s p).height = p.height := by
  exact (coefficient_localization_prime_height (F := FractionRing (MvPolynomial s K))
    (p.comap (coordinateSplit (K := K) s).symm.toRingHom)
    (coordinateSplit_comap_coefficients_eq_bot_of_fractionField s p hs)).2.trans
    ((coordinateSplit (K := K) s).symm.toRingEquiv.height_comap p)

noncomputable def coordinateFractionLocalEquiv {K σ : Type*} [Field K]
    (s : Set σ) (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    [(coordinateLocalizedPrime s p).IsPrime]
    (hs : AlgebraicIndependent K (fun i : s =>
      algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
        (Ideal.Quotient.mk p (MvPolynomial.X i)))) :
    Localization.AtPrime p ≃ₐ[K] Localization.AtPrime (coordinateLocalizedPrime s p) := by
  have : ((p.comap (coordinateSplit (K := K) s).symm.toRingHom).map
      (algebraMap (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K))
        (MvPolynomial (sᶜ : Set σ) (FractionRing (MvPolynomial s K))))).IsPrime :=
    ‹(coordinateLocalizedPrime s p).IsPrime›
  letI : IsScalarTower K (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K))
      (Localization.AtPrime (coordinateLocalizedPrime s p)) :=
    IsScalarTower.to₁₂₄ K (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K))
      (MvPolynomial (sᶜ : Set σ) (FractionRing (MvPolynomial s K)))
      (Localization.AtPrime (coordinateLocalizedPrime s p))
  exact (coordinateSplitLocalEquiv s p).trans
    ((coefficientLocalizationLocalEquiv (F := FractionRing (MvPolynomial s K))
      (p.comap (coordinateSplit (K := K) s).symm.toRingHom)
      (coordinateSplit_comap_coefficients_eq_bot_of_fractionField s p hs)).restrictScalars K)

theorem coordinateFraction_localEquiv_algebraMap {K σ : Type*} [Field K]
    (s : Set σ) (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    [(coordinateLocalizedPrime s p).IsPrime]
    (hs : AlgebraicIndependent K (fun i : s =>
      algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
        (Ideal.Quotient.mk p (MvPolynomial.X i)))) (f : MvPolynomial σ K) :
    coordinateFractionLocalEquiv s p hs (algebraMap _ (Localization.AtPrime p) f) =
      algebraMap _ (Localization.AtPrime (coordinateLocalizedPrime s p))
        (MvPolynomial.map (algebraMap (MvPolynomial s K) (FractionRing (MvPolynomial s K)))
          (coordinateSplit s f)) := by
  have : ((p.comap (coordinateSplit (K := K) s).symm.toRingHom).map
      (algebraMap (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K))
        (MvPolynomial (sᶜ : Set σ) (FractionRing (MvPolynomial s K))))).IsPrime :=
    ‹(coordinateLocalizedPrime s p).IsPrime›
  have hsplit : coordinateSplitLocalEquiv s p (algebraMap _ (Localization.AtPrime p) f) =
      algebraMap _ (Localization.AtPrime (p.comap (coordinateSplit (K := K) s).symm.toRingHom))
        (coordinateSplit s f) := by
    apply (coordinateSplitLocalEquiv s p).symm.injective
    rw [AlgEquiv.symm_apply_apply]
    change algebraMap _ (Localization.AtPrime p) f =
      Localization.localRingHom _ p (coordinateSplit (K := K) s).symm.toRingHom rfl
        (algebraMap _ _ (coordinateSplit s f))
    rw [Localization.localRingHom_to_map]
    change algebraMap _ (Localization.AtPrime p) f =
      algebraMap _ (Localization.AtPrime p) ((coordinateSplit s).symm (coordinateSplit s f))
    rw [AlgEquiv.symm_apply_apply]
  change (coefficientLocalizationLocalEquiv
      (F := FractionRing (MvPolynomial s K))
      (p.comap (coordinateSplit (K := K) s).symm.toRingHom)
      (coordinateSplit_comap_coefficients_eq_bot_of_fractionField s p hs))
    (coordinateSplitLocalEquiv s p (algebraMap _ (Localization.AtPrime p) f)) = _
  rw [hsplit, AlgEquiv.commutes]
  rfl

theorem coordinateLocalizedPrime_finite_quotient {K σ : Type*} [Field K] [Finite σ]
    (s : Set σ) (p : Ideal (MvPolynomial σ K))
    [(coordinateLocalizedPrime s p).IsMaximal] :
    Module.Finite (FractionRing (MvPolynomial s K))
      (MvPolynomial (sᶜ : Set σ) (FractionRing (MvPolynomial s K)) ⧸
        coordinateLocalizedPrime s p) := by
  let := Ideal.Quotient.field (coordinateLocalizedPrime s p)
  exact finite_of_finite_type_of_isJacobsonRing _ _

theorem coordinate_complement_card_eq_height {K σ : Type*} [Field K] [Finite σ]
    (s : Set σ) (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    [(coordinateLocalizedPrime s p).IsMaximal]
    (hs : AlgebraicIndependent K (fun i : s =>
      algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
        (Ideal.Quotient.mk p (MvPolynomial.X i)))) :
    (Nat.card (sᶜ : Set σ) : ℕ∞) = p.height := by
  let := Fintype.ofFinite (sᶜ : Set σ)
  rw [← coordinateLocalizedPrime_height s p hs, maximal_mvPolynomial_height]
  simp only [Nat.card_eq_fintype_card]

theorem exists_coordinate_localization {K σ : Type*} [Field K] [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    ∃ (s : Set σ)
      (_hs : IsTranscendenceBasis K (fun i : s => componentCoordinate p i))
      (hq : (coordinateLocalizedPrime s p).IsMaximal),
      letI := hq
      Module.Finite (FractionRing (MvPolynomial s K))
        (MvPolynomial (sᶜ : Set σ) (FractionRing (MvPolynomial s K)) ⧸
          coordinateLocalizedPrime s p) ∧
      (Nat.card (sᶜ : Set σ) : ℕ∞) = p.height ∧
      ∃ e : Localization.AtPrime p ≃ₐ[K] Localization.AtPrime (coordinateLocalizedPrime s p),
        ∀ f : MvPolynomial σ K,
          e (algebraMap _ (Localization.AtPrime p) f) =
            algebraMap _ (Localization.AtPrime (coordinateLocalizedPrime s p))
              (MvPolynomial.map
                (algebraMap (MvPolynomial s K) (FractionRing (MvPolynomial s K)))
                (coordinateSplit s f)) ∧
          (MvPolynomial.map
            (algebraMap (MvPolynomial s K) (FractionRing (MvPolynomial s K)))
            (coordinateSplit s f)).totalDegree ≤ f.totalDegree := by
  obtain ⟨s, hs⟩ := exists_prime_quotient_coordinate_basis p
  have hq : (coordinateLocalizedPrime s p).IsMaximal :=
    coordinateSplit_localized_prime_isMaximal s p hs
  refine ⟨s, hs, hq, coordinateLocalizedPrime_finite_quotient s p,
    coordinate_complement_card_eq_height s p hs.1, coordinateFractionLocalEquiv s p hs.1, ?_⟩
  intro f
  exact ⟨coordinateFraction_localEquiv_algebraMap s p hs.1 f,
    totalDegree_localized_coordinateSplit_le s f⟩

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry.DegreeBezout

theorem ring_length_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) : Module.length A A = Module.length B B := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let f : A ≃ₗ[A] B :=
    { e.toAddEquiv with map_smul' := by intro a b; exact e.map_mul a b }
  rw [← Module.length_eq_of_surjective (M := B) e.surjective]
  exact f.length_eq

theorem quotient_length_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) (J : Ideal B)
    (hJ : J = I.map e.toRingHom) :
    Module.length A (A ⧸ I) = Module.length B (B ⧸ J) := by
  rw [Module.length_eq_of_surjective (S := A) (R := A ⧸ I) (M := A ⧸ I)
      (Ideal.Quotient.mk_surjective (I := I)),
    Module.length_eq_of_surjective (S := B) (R := B ⧸ J) (M := B ⧸ J)
      (Ideal.Quotient.mk_surjective (I := J))]
  exact ring_length_eq_of_ringEquiv (Ideal.quotientEquiv I J e hJ)

end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.Geometry

theorem radical_map_ringEquiv_eq_maximalIdeal
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (I : Ideal A)
    (hI : I.radical = IsLocalRing.maximalIdeal A) :
    (I.map e.toRingHom).radical = IsLocalRing.maximalIdeal B := by
  have hk : RingHom.ker e.toRingHom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot e.toRingHom).mp e.injective
  rw [← Ideal.map_radical_of_surjective e.surjective
    (hk ▸ bot_le), hI]
  exact IsLocalRing.map_ringEquiv_maximalIdeal e

theorem map_span_range_of_commuting_images
    {A B ι : Type*} [CommRing A] [CommRing B]
    (e : A →+* B) (f : ι → A) (g : ι → B) (h : ∀ i, e (f i) = g i) :
    (Ideal.span (Set.range f)).map e = Ideal.span (Set.range g) := by
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  exact congrArg Set.range (funext h)

theorem quotient_length_eq_of_commuting_images
    {A B ι : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (f : ι → A) (g : ι → B) (h : ∀ i, e (f i) = g i) :
    Module.length A (A ⧸ Ideal.span (Set.range f)) =
      Module.length B (B ⧸ Ideal.span (Set.range g)) := by
  exact DegreeBezout.quotient_length_eq_of_ringEquiv e _ _
    (map_span_range_of_commuting_images e.toRingHom f g h).symm

theorem radical_span_eq_maximalIdeal_of_commuting_images
    {A B ι : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (f : ι → A) (g : ι → B) (h : ∀ i, e (f i) = g i)
    (hf : (Ideal.span (Set.range f)).radical = IsLocalRing.maximalIdeal A) :
    (Ideal.span (Set.range g)).radical = IsLocalRing.maximalIdeal B := by
  rw [← map_span_range_of_commuting_images e.toRingHom f g h]
  exact radical_map_ringEquiv_eq_maximalIdeal e _ hf

noncomputable def polynomialRenameLocalEquiv
    {K σ τ : Type*} [Field K] (e : σ ≃ τ)
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    Localization.AtPrime p ≃+*
      Localization.AtPrime (p.comap (MvPolynomial.renameEquiv K e).symm.toRingHom) :=
  (Localization.localRingEquiv _ p (MvPolynomial.renameEquiv K e).symm.toRingEquiv rfl).symm

theorem polynomialRename_localEquiv_algebraMap
    {K σ τ : Type*} [Field K] (e : σ ≃ τ)
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (f : MvPolynomial σ K) :
    polynomialRenameLocalEquiv e p (algebraMap _ (Localization.AtPrime p) f) =
      algebraMap _ (Localization.AtPrime
        (p.comap (MvPolynomial.renameEquiv K e).symm.toRingHom))
          (MvPolynomial.renameEquiv K e f) := by
  apply (polynomialRenameLocalEquiv e p).symm.injective
  rw [RingEquiv.symm_apply_apply]
  change algebraMap _ (Localization.AtPrime p) f =
    Localization.localRingHom _ p (MvPolynomial.renameEquiv K e).symm.toRingHom rfl
      (algebraMap _ _ (MvPolynomial.renameEquiv K e f))
  rw [Localization.localRingHom_to_map]
  exact congrArg (algebraMap _ (Localization.AtPrime p))
    ((MvPolynomial.renameEquiv K e).symm_apply_apply f).symm

theorem maximal_local_bound_of_card_eq
    {K σ : Type*} [Field K] [Finite σ] (h d : ℕ)
    (hbound : ∀ (q : Ideal (MvPolynomial (Fin h) K)) [q.IsMaximal]
      (g : Fin h → MvPolynomial (Fin h) K),
      (∀ i, (g i).totalDegree ≤ d) →
      (Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime q) (g i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime q) →
      Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⧸ Ideal.span
          (Set.range (fun i => algebraMap _ (Localization.AtPrime q) (g i)))) ≤ (d ^ h : ℕ∞))
    (p : Ideal (MvPolynomial σ K)) [p.IsMaximal]
    (hcard : Nat.card σ = h) (f : Fin h → MvPolynomial σ K)
    (hf : ∀ i, (f i).totalDegree ≤ d)
    (hrad : (Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime p) (f i)))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ Ideal.span
        (Set.range (fun i => algebraMap _ (Localization.AtPrime p) (f i)))) ≤ (d ^ h : ℕ∞) := by
  let := Fintype.ofFinite σ
  let e : σ ≃ Fin h := Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let q := p.comap (MvPolynomial.renameEquiv K e).symm.toRingHom
  have : q.IsMaximal := Ideal.comap_isMaximal_of_surjective
    (MvPolynomial.renameEquiv K e).symm.toRingHom (MvPolynomial.renameEquiv K e).symm.surjective
  let g : Fin h → MvPolynomial (Fin h) K := fun i => MvPolynomial.renameEquiv K e (f i)
  have hg : ∀ i, (g i).totalDegree ≤ d := by
    intro i
    exact (MvPolynomial.totalDegree_renameEquiv e (f i)) ▸ hf i
  let he := polynomialRenameLocalEquiv e p
  have hcomm (i : Fin h) : he (algebraMap _ (Localization.AtPrime p) (f i)) =
      algebraMap _ (Localization.AtPrime q) (g i) := polynomialRename_localEquiv_algebraMap e p (f i)
  have hrad' := radical_span_eq_maximalIdeal_of_commuting_images he _ _ hcomm hrad
  rw [quotient_length_eq_of_commuting_images he _ _ hcomm]
  exact hbound q g hg hrad'

theorem local_parameter_bound_of_isLocalization_atPrime
    {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime A p] [IsLocalRing A]
    (f : ι → R) (B : ℕ∞)
    (hbound : (Ideal.span (Set.range (fun i => algebraMap R (Localization.AtPrime p) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) →
      Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ Ideal.span
          (Set.range (fun i => algebraMap R (Localization.AtPrime p) (f i)))) ≤ B)
    (hrad : (Ideal.span (Set.range (fun i => algebraMap R A (f i)))).radical =
      IsLocalRing.maximalIdeal A) :
    Module.length A (A ⧸ Ideal.span (Set.range (fun i => algebraMap R A (f i)))) ≤ B := by
  let e := IsLocalization.algEquiv p.primeCompl A (Localization.AtPrime p)
  have hcomm (i : ι) : e (algebraMap R A (f i)) =
      algebraMap R (Localization.AtPrime p) (f i) := e.commutes (f i)
  have hrad' := radical_span_eq_maximalIdeal_of_commuting_images e.toRingEquiv _ _ hcomm hrad
  rw [quotient_length_eq_of_commuting_images e.toRingEquiv _ _ hcomm]
  exact hbound hrad'



universe u v w

theorem arbitrary_prime_bound_of_maximal_local_bound
    {K : Type u} {σ : Type v} [Field K] [Finite σ] (h d : ℕ)
    (hbound : ∀ (F : Type (max u v)) [Field F]
      (q : Ideal (MvPolynomial (Fin h) F)) [q.IsMaximal]
      (g : Fin h → MvPolynomial (Fin h) F),
      (∀ i, (g i).totalDegree ≤ d) →
      (Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime q) (g i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime q) →
      Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⧸ Ideal.span
          (Set.range (fun i => algebraMap _ (Localization.AtPrime q) (g i)))) ≤ (d ^ h : ℕ∞))
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (hheight : p.height = (h : ℕ∞))
    (f : Fin h → MvPolynomial σ K) (hf : ∀ i, (f i).totalDegree ≤ d)
    (hrad : (Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime p) (f i)))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ Ideal.span
        (Set.range (fun i => algebraMap _ (Localization.AtPrime p) (f i)))) ≤ (d ^ h : ℕ∞) := by
  obtain ⟨s, hs, hq, hrest⟩ := exists_coordinate_localization p
  let := hq
  obtain ⟨_, hcard, e, he⟩ := hrest
  let g : Fin h → MvPolynomial (sᶜ : Set σ) (FractionRing (MvPolynomial s K)) :=
    fun i => MvPolynomial.map
      (algebraMap (MvPolynomial s K) (FractionRing (MvPolynomial s K))) (coordinateSplit s (f i))
  have hg : ∀ i, (g i).totalDegree ≤ d := fun i => (he (f i)).2.trans (hf i)
  have hcomm (i : Fin h) : e (algebraMap _ (Localization.AtPrime p) (f i)) =
      algebraMap _ (Localization.AtPrime (coordinateLocalizedPrime s p)) (g i) := (he (f i)).1
  let eR : Localization.AtPrime p ≃+* Localization.AtPrime (coordinateLocalizedPrime s p) :=
    e.toRingEquiv
  have hrad' := radical_span_eq_maximalIdeal_of_commuting_images eR
    (fun i => algebraMap _ (Localization.AtPrime p) (f i))
    (fun i => algebraMap _ (Localization.AtPrime (coordinateLocalizedPrime s p)) (g i))
    (fun i => hcomm i) hrad
  rw [quotient_length_eq_of_commuting_images eR
    (fun i => algebraMap _ (Localization.AtPrime p) (f i))
    (fun i => algebraMap _ (Localization.AtPrime (coordinateLocalizedPrime s p)) (g i))
    (fun i => hcomm i)]
  apply maximal_local_bound_of_card_eq h d (hbound (FractionRing (MvPolynomial s K))) (coordinateLocalizedPrime s p) _ g hg hrad'
  exact WithTop.coe_eq_coe.mp (hcard.trans hheight)

theorem arbitrary_local_bound_of_maximal_local_bound
    {K : Type u} {σ : Type v} {A : Type w} [Field K] [Finite σ] [CommRing A] [Algebra (MvPolynomial σ K) A]
    (h d : ℕ)
    (hbound : ∀ (F : Type (max u v)) [Field F]
      (q : Ideal (MvPolynomial (Fin h) F)) [q.IsMaximal]
      (g : Fin h → MvPolynomial (Fin h) F),
      (∀ i, (g i).totalDegree ≤ d) →
      (Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime q) (g i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime q) →
      Module.length (Localization.AtPrime q)
        (Localization.AtPrime q ⧸ Ideal.span
          (Set.range (fun i => algebraMap _ (Localization.AtPrime q) (g i)))) ≤ (d ^ h : ℕ∞))
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] [IsLocalization.AtPrime A p] [IsLocalRing A]
    (hheight : p.height = (h : ℕ∞))
    (f : Fin h → MvPolynomial σ K) (hf : ∀ i, (f i).totalDegree ≤ d)
    (hrad : (Ideal.span (Set.range (fun i => algebraMap (MvPolynomial σ K) A (f i)))).radical =
      IsLocalRing.maximalIdeal A) :
    Module.length A (A ⧸ Ideal.span
      (Set.range (fun i => algebraMap (MvPolynomial σ K) A (f i)))) ≤ (d ^ h : ℕ∞) := by
  apply local_parameter_bound_of_isLocalization_atPrime p f (d ^ h)
    (fun hrad' => arbitrary_prime_bound_of_maximal_local_bound h d hbound p hheight f hf hrad') hrad




universe uSource
variable {K : Type uSource} [Field K] [Infinite K]
local notation "P₄" => MvPolynomial (Fin 4) K
local notation "T₄" => Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : P₄))


end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry.DegreeBezout
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem coefficient_residue_injective
    {B σ : Type*} [CommRing B]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    (hp : p.comap MvPolynomial.C = ⊥) :
    Function.Injective (algebraMap B p.ResidueField) := by
  rw [RingHom.injective_iff_ker_eq_bot,
    IsScalarTower.algebraMap_eq B (MvPolynomial σ B) p.ResidueField,
    ← RingHom.comap_ker, Ideal.ker_algebraMap_residueField]
  exact hp

@[instance_reducible] noncomputable def componentCoefficientFractionAlgebra
    {B F σ : Type*} [CommRing B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    (hp : p.comap MvPolynomial.C = ⊥) : Algebra F p.ResidueField :=
  (IsFractionRing.lift (K := F) (coefficient_residue_injective p hp)).toAlgebra

theorem componentCoefficientFractionAlgebra_tower
    {B F σ : Type*} [CommRing B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    (hp : p.comap MvPolynomial.C = ⊥) :
    letI := componentCoefficientFractionAlgebra (F := F) p hp
    IsScalarTower B F p.ResidueField := by
  let := componentCoefficientFractionAlgebra (F := F) p hp
  apply IsScalarTower.of_algebraMap_eq
  intro b
  exact (IsFractionRing.lift_algebraMap (K := F) (coefficient_residue_injective p hp) b).symm

theorem component_functionField_finite
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [Module.Finite B (MvPolynomial σ B ⧸ p)]
    (hp : p.comap MvPolynomial.C = ⊥) :
    letI := componentCoefficientFractionAlgebra (F := F) p hp
    Module.Finite F p.ResidueField := by
  let := componentCoefficientFractionAlgebra (F := F) p hp
  let := componentCoefficientFractionAlgebra_tower (F := F) p hp
  have hb : Function.Injective (algebraMap B (MvPolynomial σ B ⧸ p)) := by
    intro x y hxy
    apply coefficient_residue_injective p hp
    rw [IsScalarTower.algebraMap_apply B (MvPolynomial σ B ⧸ p) p.ResidueField,
      IsScalarTower.algebraMap_apply B (MvPolynomial σ B ⧸ p) p.ResidueField, hxy]
  let : FaithfulSMul B (MvPolynomial σ B ⧸ p) :=
    (faithfulSMul_iff_algebraMap_injective B (MvPolynomial σ B ⧸ p)).mpr hb
  apply Module.finite_of_finrank_pos
  rw [IsFractionRing.finrank_eq B F (MvPolynomial σ B ⧸ p) p.ResidueField]
  exact Module.finrank_pos

theorem coefficient_localization_isMaximal_of_finite
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [Module.Finite B (MvPolynomial σ B ⧸ p)]
    (hp : p.comap MvPolynomial.C = ⊥) :
    (p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsMaximal := by
  let := componentCoefficientFractionAlgebra (F := F) p hp
  let := componentCoefficientFractionAlgebra_tower (F := F) p hp
  let := component_functionField_finite (F := F) p hp
  let M : Submonoid (MvPolynomial σ B) := (nonZeroDivisors B).map MvPolynomial.C
  let g := IsScalarTower.toAlgHom B (MvPolynomial σ B) p.ResidueField
  have hu : ∀ y : M, IsUnit (g y) := by
    intro y
    apply isUnit_iff_ne_zero.mpr
    intro hy
    have hyp : (y : MvPolynomial σ B) ∈ p :=
      Ideal.algebraMap_residueField_eq_zero.mp hy
    exact Set.disjoint_left.mp (coefficient_nonZeroDivisors_disjoint p hp) y.property hyp
  let fB : MvPolynomial σ F →ₐ[B] p.ResidueField := IsLocalization.liftAlgHom hu
  let f := fB.extendScalarsOfIsLocalization F (nonZeroDivisors B)
  have he : f.toRingHom.comp (algebraMap (MvPolynomial σ B) (MvPolynomial σ F)) =
      algebraMap (MvPolynomial σ B) p.ResidueField := by
    exact IsLocalization.lift_comp hu
  apply coefficient_localization_isMaximal p f
  change (RingHom.ker f.toRingHom).comap
    (algebraMap (MvPolynomial σ B) (MvPolynomial σ F)) = p
  rw [RingHom.comap_ker, he, Ideal.ker_algebraMap_residueField]

end WeightedTorusJets.Geometry.DegreeBezout


namespace WeightedTorusJets.Geometry.DegreeBezout

open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K σ ι τ : Type*} [CommRing K]

def normalizationPresentation
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial τ (MvPolynomial ι K) :=
  e.symm.trans ((renameEquiv K (Equiv.sumComm ι τ)).trans (sumAlgEquiv K τ ι))

@[simp] theorem normalizationPresentation_symm_C_X
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K) (i : ι) :
    (normalizationPresentation e).symm (C (X i)) = e (X (Sum.inl i)) := by
  simp [normalizationPresentation]

@[simp] theorem normalizationPresentation_symm_X
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K) (j : τ) :
    (normalizationPresentation e).symm (X j) = e (X (Sum.inr j)) := by
  simp [normalizationPresentation]

theorem normalizationPresentation_coefficient_map
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (P : Ideal (MvPolynomial σ K))
    (g : MvPolynomial ι K →ₐ[K] (MvPolynomial σ K ⧸ P))
    (hg : ∀ i, g (X i) = Ideal.Quotient.mk P (e (X (Sum.inl i))))
    (b : MvPolynomial ι K) :
    Ideal.Quotient.mk P ((normalizationPresentation e).symm (C b)) = g b := by
  have h : (Ideal.Quotient.mkₐ K P).comp
      ((normalizationPresentation e).symm.toAlgHom.comp
        (IsScalarTower.toAlgHom K (MvPolynomial ι K)
          (MvPolynomial τ (MvPolynomial ι K)))) = g := by
    ext i
    change Ideal.Quotient.mk P ((normalizationPresentation e).symm (C (X i))) = g (X i)
    rw [normalizationPresentation_symm_C_X]
    exact (hg i).symm
  exact congrArg (fun f : MvPolynomial ι K →ₐ[K] (MvPolynomial σ K ⧸ P) => f b) h

def normalizationPresentationQuotientEquiv
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (P : Ideal (MvPolynomial σ K))
    (g : MvPolynomial ι K →ₐ[K] (MvPolynomial σ K ⧸ P))
    (hg : ∀ i, g (X i) = Ideal.Quotient.mk P (e (X (Sum.inl i)))) :
    let := g.toAlgebra
    (MvPolynomial τ (MvPolynomial ι K) ⧸
      P.comap (normalizationPresentation e).symm.toRingHom) ≃ₐ[MvPolynomial ι K]
      (MvPolynomial σ K ⧸ P) := by
  let := g.toAlgebra
  let q := P.comap (normalizationPresentation e).symm.toRingHom
  let eQ : (MvPolynomial τ (MvPolynomial ι K) ⧸ q) ≃ₐ[K]
      (MvPolynomial σ K ⧸ P) :=
    Ideal.quotientEquivAlg q P (normalizationPresentation e).symm
      (Ideal.map_comap_of_surjective (normalizationPresentation e).symm.toRingHom
        (normalizationPresentation e).symm.surjective P).symm
  refine { eQ.toRingEquiv with commutes' := ?_ }
  intro b
  change eQ (Ideal.Quotient.mk q (C b)) = g b
  change Ideal.Quotient.mk P ((normalizationPresentation e).symm (C b)) = g b
  exact normalizationPresentation_coefficient_map e P g hg b

theorem normalizationPresentation_coefficient_comap_eq_bot
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (P : Ideal (MvPolynomial σ K))
    (g : MvPolynomial ι K →ₐ[K] (MvPolynomial σ K ⧸ P))
    (hginj : Function.Injective g)
    (hg : ∀ i, g (X i) = Ideal.Quotient.mk P (e (X (Sum.inl i)))) :
    (P.comap (normalizationPresentation e).symm.toRingHom).comap C = ⊥ := by
  apply bot_unique
  intro b hb
  apply hginj
  rw [map_zero, ← normalizationPresentation_coefficient_map e P g hg b]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hb

theorem finite_normalizationPresentation_quotient
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (P : Ideal (MvPolynomial σ K))
    (g : MvPolynomial ι K →ₐ[K] (MvPolynomial σ K ⧸ P))
    (hg : ∀ i, g (X i) = Ideal.Quotient.mk P (e (X (Sum.inl i))))
    (hfinite : letI := g.toAlgebra
      letI : Module (MvPolynomial ι K) (MvPolynomial σ K ⧸ P) := Algebra.toModule
      Module.Finite (MvPolynomial ι K) (MvPolynomial σ K ⧸ P)) :
    Module.Finite (MvPolynomial ι K)
      (MvPolynomial τ (MvPolynomial ι K) ⧸
        P.comap (normalizationPresentation e).symm.toRingHom) := by
  let := g.toAlgebra
  let : Module (MvPolynomial ι K) (MvPolynomial σ K ⧸ P) := Algebra.toModule
  have : Module.Finite (MvPolynomial ι K) (MvPolynomial σ K ⧸ P) := hfinite
  exact Module.Finite.equiv (normalizationPresentationQuotientEquiv e P g hg).symm.toLinearEquiv

end WeightedTorusJets.Geometry.DegreeBezout

end

end SiegelZeros

end OAI
