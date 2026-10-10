import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Differentials.InvariantDerivationLemmas

namespace OAI

namespace SiegelZeros

open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
open scoped BigOperators
namespace WeightedTorusJets.Geometry

noncomputable def polynomialBox (K : Type*) [Field K] (N : ℕ) :
    Submodule K (MvPolynomial (Fin 4) K) :=
  Submodule.span K (Set.range fun n : Fin 4 → Fin N =>
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (n i : ℕ)) 1)

theorem totalDegree_lt_of_mem_polynomialBox {K : Type*} [Field K] {N : ℕ}
    (hN : 0 < N) {F : MvPolynomial (Fin 4) K} (hF : F ∈ polynomialBox K N) :
    F.totalDegree < 4 * N := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
      obtain ⟨n, rfl⟩ := hF
      change (MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm fun i => (n i : ℕ)) (1 : K)).totalDegree < _
      rw [MvPolynomial.totalDegree_monomial _ one_ne_zero, Finsupp.sum_fintype]
      · simpa using Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
          Finset.univ_nonempty (fun i _ ↦ (n i).isLt)
      · simp
  | zero => simp [Nat.mul_pos (by decide : 0 < 4) hN]
  | add F G _ _ hF hG =>
      exact (MvPolynomial.totalDegree_add F G).trans_lt (max_lt hF hG)
  | smul a F _ hF => exact (MvPolynomial.totalDegree_smul_le a F).trans_lt hF



def rectangleJetIdeal {ι R : Type*} [CommRing R]
    (jet : (ι → ℕ) → R) (t : ι → ℕ) (b : ℕ) : Ideal R :=
  Ideal.span (jet '' {a | ∀ j, a j ≤ b * t j})

theorem rectangleJetIdeal_map {ι R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (jet : (ι → ℕ) → R) (t : ι → ℕ) (b : ℕ) :
    (rectangleJetIdeal jet t b).map f = rectangleJetIdeal (fun a => f (jet a)) t b := by
  simp only [rectangleJetIdeal, Ideal.map_span, Set.image_image]

theorem polynomial_prime_height_eq_cotangent_finrank
    {K σ A : Type*} [Field K] [Finite σ] [CommRing A] [IsLocalRing A]
    [Algebra (MvPolynomial σ K) A]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] [IsLocalization.AtPrime A p] :
    p.height = (Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.CotangentSpace A) : ℕ∞) := by
  have : IsRegularLocalRing A := IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) A).toRingEquiv
  apply WithBot.coe_injective
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height p A,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, regular_local_maximal_height]

theorem rectangleJetIdeal_exists_parameters_with_length
    {K A : Type*} [Field K] [Infinite K] [CommRing A] [IsLocalRing A]
    [Algebra K A] [Algebra (MvPolynomial (Fin 4) K) A]
    [IsScalarTower K (MvPolynomial (Fin 4) K) A]
    [Algebra (Localization (Submonoid.powers
      (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)))) A]
    [IsScalarTower (MvPolynomial (Fin 4) K)
      (Localization (Submonoid.powers
        (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)))) A]
    (p : Ideal (Localization (Submonoid.powers
      (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)))))
    [p.IsPrime] [IsLocalization.AtPrime A p]
    (c : Fin 3 → Fin 4 → K) (t : Fin 3 → ℕ) (b : ℕ)
    {N : ℕ} (hN : 0 < N) {F : MvPolynomial (Fin 4) K}
    (hF : F ∈ polynomialBox K N)
    (hp : p ∈ (rectangleJetIdeal
      (fun a => algebraMap _ _ (invariantJet c a F)) t b).minimalPrimes) :
    ∃ g : Fin (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A)) →
        MvPolynomial (Fin 4) K,
      (∀ i, g i ∈ Submodule.span K
        ((fun a => invariantJet c a F) '' {a | ∀ j, a j ≤ b * t j})) ∧
      (∀ i, (g i).totalDegree ≤ 4 * N) ∧
      (Ideal.span (Set.range (fun i => algebraMap (MvPolynomial (Fin 4) K) A (g i)))).radical =
        IsLocalRing.maximalIdeal A ∧
      Module.length A (A ⧸ (rectangleJetIdeal
        (fun a => algebraMap (MvPolynomial (Fin 4) K)
          (Localization (Submonoid.powers
            (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K))))
          (invariantJet c a F)) t b).map
          (algebraMap (Localization (Submonoid.powers
            (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)))) A)) ≤
        Module.length A (A ⧸ Ideal.span
          (Set.range (fun i => algebraMap (MvPolynomial (Fin 4) K) A (g i)))) ∧
      Module.length A (A ⧸ Ideal.span
        (Set.range (fun i => algebraMap (MvPolynomial (Fin 4) K) A (g i)))) ≠ ⊤ := by
  let M := Submonoid.powers (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K))
  let S := (fun a => invariantJet c a F) '' {a | ∀ j, a j ≤ b * t j}
  have hS : ∀ f ∈ S, f.totalDegree ≤ 4 * N := by
    rintro f ⟨a, _, rfl⟩
    exact (totalDegree_invariantJet_le c a F).trans
      (totalDegree_lt_of_mem_polynomialBox hN hF).le
  have hp' : p ∈ ((Ideal.span S).map
      (algebraMap (MvPolynomial (Fin 4) K) (Localization M))).minimalPrimes := by
    change p ∈ ((rectangleJetIdeal (fun a => invariantJet c a F) t b).map _).minimalPrimes
    rwa [rectangleJetIdeal_map]
  obtain ⟨g, hg, hd, _, hrad, hle, hfin⟩ :=
    polynomial_parameters_with_finite_length (A := A) M p S hp' (4 * N) hS
  have hlocal : (Ideal.span S).map (algebraMap (MvPolynomial (Fin 4) K) A) =
      (rectangleJetIdeal (fun a => algebraMap (MvPolynomial (Fin 4) K) (Localization M)
        (invariantJet c a F)) t b).map (algebraMap (Localization M) A) := by
    change (rectangleJetIdeal (fun a => invariantJet c a F) t b).map _ = _
    rw [rectangleJetIdeal_map, rectangleJetIdeal_map]
    simp only [← IsScalarTower.algebraMap_apply (MvPolynomial (Fin 4) K) (Localization M) A]
  refine ⟨g, hg, hd, hrad, ?_, hfin⟩
  rw [← (Ideal.quotientEquivAlgOfEq A hlocal).toLinearEquiv.length_eq]
  exact hle


variable {K : Type*} [Field K] [Infinite K]
local notation "P₄" => MvPolynomial (Fin 4) K
local notation "T₄" => Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : P₄))

theorem torus_rectangleJetIdeal_exists_bounded_parameters
    (p : Ideal T₄) [p.IsPrime] (c : Fin 3 → Fin 4 → K) (t : Fin 3 → ℕ) (b : ℕ)
    {N : ℕ} (hN : 0 < N) {F : P₄} (hF : F ∈ polynomialBox K N)
    (hp : p ∈ (rectangleJetIdeal (fun a => algebraMap P₄ T₄ (invariantJet c a F)) t b).minimalPrimes) :
    ∃ g : Fin (Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime p))
        (IsLocalRing.CotangentSpace (Localization.AtPrime p))) → P₄,
      (∀ i, (g i).totalDegree ≤ 4 * N) ∧
      (Ideal.span (Set.range (fun i => algebraMap P₄ (Localization.AtPrime p) (g i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∧
      Module.length (Localization.AtPrime p) (Localization.AtPrime p ⧸
        (rectangleJetIdeal (fun a => algebraMap P₄ T₄ (invariantJet c a F)) t b).map
          (algebraMap T₄ (Localization.AtPrime p))) ≤
      Module.length (Localization.AtPrime p) (Localization.AtPrime p ⧸
        Ideal.span (Set.range (fun i => algebraMap P₄ (Localization.AtPrime p) (g i)))) := by
  obtain ⟨g, _, hd, hrad, hle, _⟩ := rectangleJetIdeal_exists_parameters_with_length
    (A := Localization.AtPrime p) p c t b hN hF hp
  exact ⟨g, hd, hrad, hle⟩


end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem adjoin_fractionField_coordinates
    {K R L ι : Type*} [Field K] [CommRing R] [Field L]
    [Algebra K R] [Algebra R L] [Algebra K L] [IsScalarTower K R L]
    [IsFractionRing R L] (x : ι → R)
    (hgen : Algebra.adjoin K (Set.range x) = ⊤) :
    IntermediateField.adjoin K (Set.range (fun i => algebraMap R L (x i))) = ⊤ := by
  let E := IntermediateField.adjoin K (Set.range (fun i => algebraMap R L (x i)))
  have hR : (IsScalarTower.toAlgHom K R L).range ≤ E.toSubalgebra := by
    rw [← Algebra.map_top, ← hgen, AlgHom.map_adjoin]
    apply Algebra.adjoin_le
    rintro _ ⟨r, ⟨i, rfl⟩, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
  apply top_le_iff.mp
  intro z _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective R z
  exact E.div_mem (hR ⟨a, rfl⟩) (hR ⟨b, rfl⟩)

theorem adjoin_quotient_coordinates
    {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K)) :
    Algebra.adjoin K (Set.range (fun i => Ideal.Quotient.mk I (MvPolynomial.X i))) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  have h : MvPolynomial.aeval (fun i => Ideal.Quotient.mk I (MvPolynomial.X i)) =
      Ideal.Quotient.mkₐ K I := by
    ext i
    simp
  rw [h]
  exact (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective K I)

theorem exists_coordinate_transcendence_basis
    {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    (x : ι → L) (hgen : IntermediateField.adjoin K (Set.range x) = ⊤) :
    ∃ s : Set ι, IsTranscendenceBasis K (fun i : s => x i) := by
  have : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) L := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, hgen,
      Algebra.isAlgebraic_iff_isIntegral]
    exact Algebra.isIntegral_of_surjective IntermediateField.topEquiv.surjective
  obtain ⟨t, htr, ht⟩ := exists_isTranscendenceBasis_subset (R := K) (Set.range x)
  obtain ⟨s, rfl, hxs⟩ := Set.exists_image_eq_injOn_of_subset_range htr
  exact ⟨s, (isTranscendenceBasis_image hxs).mpr ht⟩

theorem exists_prime_quotient_coordinate_basis
    {K σ : Type*} [Field K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    ∃ s : Set σ, IsTranscendenceBasis K (fun i : s =>
      algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
        (Ideal.Quotient.mk p (MvPolynomial.X i))) := by
  exact exists_coordinate_transcendence_basis
    (K := K) (L := FractionRing (MvPolynomial σ K ⧸ p))
    (fun i : σ => algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
      (Ideal.Quotient.mk p (MvPolynomial.X i)))
    (adjoin_fractionField_coordinates
      (K := K) (R := MvPolynomial σ K ⧸ p) (L := FractionRing (MvPolynomial σ K ⧸ p))
      (fun i : σ => Ideal.Quotient.mk p (MvPolynomial.X i)) (adjoin_quotient_coordinates p))



attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem coefficient_nonZeroDivisors_disjoint
    {B σ : Type*} [CommRing B] [IsDomain B]
    (p : Ideal (MvPolynomial σ B))
    (hp : p.comap MvPolynomial.C = ⊥) :
    Disjoint (((nonZeroDivisors B).map MvPolynomial.C :
      Submonoid (MvPolynomial σ B)) : Set (MvPolynomial σ B)) (p : Set _) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨b, hb, rfl⟩ hbp
  have hz : b = 0 := by
    have hmem : b ∈ p.comap MvPolynomial.C := hbp
    simpa [hp] using hmem
  exact (mem_nonZeroDivisors_iff_ne_zero.mp hb) hz

theorem coefficient_localization_prime_height
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    (hp : p.comap MvPolynomial.C = ⊥) :
    (p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsPrime ∧
      (p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).height = p.height := by
  let M : Submonoid (MvPolynomial σ B) :=
    (nonZeroDivisors B).map MvPolynomial.C
  have hM := coefficient_nonZeroDivisors_disjoint p hp
  exact ⟨IsLocalization.isPrime_of_isPrime_disjoint M (MvPolynomial σ F) p inferInstance hM,
    IsLocalization.height_map_of_disjoint M p hM⟩

noncomputable def coefficientLocalizationLocalEquiv
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [((p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F)))).IsPrime]
    (hp : p.comap MvPolynomial.C = ⊥) :
    Localization.AtPrime p ≃ₐ[MvPolynomial σ B]
      Localization.AtPrime (p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))) := by
  let M : Submonoid (MvPolynomial σ B) :=
    (nonZeroDivisors B).map MvPolynomial.C
  let q := p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))
  have hM := coefficient_nonZeroDivisors_disjoint p hp
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (M := M) (Localization.AtPrime q) q
  simp_rw [q, IsLocalization.under_map_of_isPrime_disjoint M (MvPolynomial σ F)
      (show p.IsPrime from inferInstance) hM]
    at this
  exact IsLocalization.algEquiv p.primeCompl _ _

theorem kernel_isMaximal_of_algebraic_field
    {F L A : Type*} [Field F] [Field L] [CommRing A]
    [Algebra F L] [Algebra F A] [Algebra.IsAlgebraic F L]
    (f : A →ₐ[F] L) : (RingHom.ker f).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  exact (Ideal.quotientKerEquivRange f).toMulEquiv.isField
    (Subalgebra.isField_of_algebraic f.range)

theorem coefficient_localization_isMaximal
    {B F L σ : Type*} [CommRing B] [Field F] [Field L]
    [Algebra B F] [IsFractionRing B F] [Algebra F L] [Algebra.IsAlgebraic F L]
    (p : Ideal (MvPolynomial σ B)) (f : MvPolynomial σ F →ₐ[F] L)
    (hp : (RingHom.ker f).comap
      (algebraMap (MvPolynomial σ B) (MvPolynomial σ F)) = p) :
    (p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsMaximal := by
  rw [← hp, IsLocalization.map_under ((nonZeroDivisors B).map MvPolynomial.C)
    (MvPolynomial σ F)]
  exact kernel_isMaximal_of_algebraic_field f

@[instance_reducible] noncomputable def coordinateFractionAlgebra
    {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    {x : σ → L} (hx : AlgebraicIndependent K x) :
    Algebra (FractionRing (MvPolynomial σ K)) L :=
  (IsFractionRing.liftAlgHom (K := FractionRing (MvPolynomial σ K))
    (algebraicIndependent_iff_injective_aeval.2 hx)).toRingHom.toAlgebra

theorem coordinateFractionAlgebra_algebraMap
    {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    {x : σ → L} (hx : AlgebraicIndependent K x) (b : MvPolynomial σ K) :
    letI := coordinateFractionAlgebra hx
    algebraMap (FractionRing (MvPolynomial σ K)) L
      (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) b) =
        MvPolynomial.aeval x b := by
  exact IsFractionRing.lift_algebraMap
    (algebraicIndependent_iff_injective_aeval.2 hx) b

theorem transcendenceBasis_isAlgebraic_coordinateFraction
    {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    {x : σ → L} (hx : IsTranscendenceBasis K x) :
    letI := coordinateFractionAlgebra hx.1
    Algebra.IsAlgebraic (FractionRing (MvPolynomial σ K)) L := by
  let := coordinateFractionAlgebra hx.1
  have := hx.isAlgebraic_field
  apply Algebra.IsAlgebraic.of_ringHom_of_comp_eq
    hx.1.aevalEquivField.toRingHom (RingHom.id L)
    hx.1.aevalEquivField.surjective Function.injective_id
  rfl

theorem coordinateFraction_aeval_comp_map
    {K L σ τ : Type*} [Field K] [Field L] [Algebra K L]
    {x : σ → L} (hx : AlgebraicIndependent K x) (y : τ → L) :
    letI := coordinateFractionAlgebra hx
    (MvPolynomial.aeval (R := FractionRing (MvPolynomial σ K)) y).toRingHom.comp
        (MvPolynomial.map (algebraMap (MvPolynomial σ K)
          (FractionRing (MvPolynomial σ K)))) =
      MvPolynomial.eval₂Hom (MvPolynomial.aeval x).toRingHom y := by
  let := coordinateFractionAlgebra hx
  apply MvPolynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C]
    change MvPolynomial.aeval (R := FractionRing (MvPolynomial σ K)) y
      (MvPolynomial.C (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) b)) =
        MvPolynomial.aeval x b
    rw [MvPolynomial.aeval_C]
    exact coordinateFractionAlgebra_algebraMap hx b
  · intro i
    simp

theorem coordinateFraction_kernel_isMaximal
    {K L σ τ : Type*} [Field K] [Field L] [Algebra K L]
    {x : σ → L} (hx : IsTranscendenceBasis K x) (y : τ → L) :
    letI := coordinateFractionAlgebra hx.1
    ((RingHom.ker (MvPolynomial.eval₂Hom (MvPolynomial.aeval x).toRingHom y)).map
      (algebraMap (MvPolynomial τ (MvPolynomial σ K))
        (MvPolynomial τ (FractionRing (MvPolynomial σ K))))).IsMaximal := by
  let := coordinateFractionAlgebra hx.1
  have := transcendenceBasis_isAlgebraic_coordinateFraction hx
  apply coefficient_localization_isMaximal _
    (MvPolynomial.aeval (R := FractionRing (MvPolynomial σ K)) y)
  change RingHom.ker ((MvPolynomial.aeval (R := FractionRing (MvPolynomial σ K)) y).toRingHom.comp
    (algebraMap (MvPolynomial τ (MvPolynomial σ K))
      (MvPolynomial τ (FractionRing (MvPolynomial σ K))))) = _
  rw [MvPolynomial.algebraMap_def, coordinateFraction_aeval_comp_map hx.1 y]

end WeightedTorusJets.Geometry

open scoped BigOperators
open MvPolynomial

namespace WeightedTorusJets.Geometry

def coordinateSplit {K σ : Type*} [CommSemiring K] (s : Set σ) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial (sᶜ : Set σ) (MvPolynomial s K) := by
  classical
  exact (renameEquiv K ((Equiv.Set.sumCompl s).symm.trans (Equiv.sumComm _ _))).trans
    (sumAlgEquiv K (sᶜ : Set σ) s)

@[simp] theorem coordinateSplit_C {K σ : Type*} [CommSemiring K]
    (s : Set σ) (c : K) : coordinateSplit s (C c) = C (C c) := by
  classical
  simp [coordinateSplit]

@[simp] theorem coordinateSplit_X_mem {K σ : Type*} [CommSemiring K]
    (s : Set σ) (i : s) : coordinateSplit (K := K) s (X i) = C (X i) := by
  classical
  simp [coordinateSplit]

@[simp] theorem coordinateSplit_X_compl {K σ : Type*} [CommSemiring K]
    (s : Set σ) (i : (sᶜ : Set σ)) : coordinateSplit (K := K) s (X i) = X i := by
  classical
  simp [coordinateSplit]

theorem coordinateSplit_symm_C {K σ : Type*} [CommSemiring K]
    (s : Set σ) (p : MvPolynomial s K) :
    (coordinateSplit s).symm (C p) = rename (Subtype.val : s → σ) p := by
  have he : (coordinateSplit (K := K) s).toAlgHom.comp
      (rename (Subtype.val : s → σ)) =
      IsScalarTower.toAlgHom K (MvPolynomial s K) (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K)) := by
    ext i
    simp
  apply (coordinateSplit s).injective
  simpa using congrArg (fun f : MvPolynomial s K →ₐ[K]
    MvPolynomial (sᶜ : Set σ) (MvPolynomial s K) => f p) he.symm

@[simp] theorem coordinateSplit_symm_X_compl {K σ : Type*} [CommSemiring K]
    (s : Set σ) (i : (sᶜ : Set σ)) :
    (coordinateSplit (K := K) s).symm (X i) = X (i : σ) := by
  apply (coordinateSplit s).injective
  simp only [AlgEquiv.apply_symm_apply, coordinateSplit_X_compl]

theorem aeval_coordinateSplit_symm
    {K A σ : Type*} [CommSemiring K] [CommSemiring A] [Algebra K A]
    (s : Set σ) (x : σ → A) (q : MvPolynomial (sᶜ : Set σ) (MvPolynomial s K)) :
    aeval x ((coordinateSplit s).symm q) =
      eval₂ (aeval (R := K) (fun i : s => x i)).toRingHom (fun i : (sᶜ : Set σ) => x i) q := by
  have he : (aeval (R := K) x).toRingHom.comp (coordinateSplit s).symm.toRingHom =
      eval₂Hom (aeval (R := K) (fun i : s => x i)).toRingHom (fun i : (sᶜ : Set σ) => x i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coordinateSplit_symm_C, aeval_rename, Function.comp_def]
    · intro i
      simp
  exact congrArg (fun f : MvPolynomial (sᶜ : Set σ) (MvPolynomial s K) →+* A => f q) he

theorem coordinateSplit_comap_coefficients_eq_bot
    {K σ : Type*} [Field K] (s : Set σ) (p : Ideal (MvPolynomial σ K))
    (hs : AlgebraicIndependent K (fun i : s => Ideal.Quotient.mk p (X i))) :
    (p.comap (coordinateSplit s).symm.toRingHom).comap
      (algebraMap (MvPolynomial s K) (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K))) = ⊥ := by
  apply bot_unique
  intro q hq
  change (coordinateSplit s).symm (C q) ∈ p at hq
  rw [coordinateSplit_symm_C] at hq
  apply hs.eq_zero_of_aeval_eq_zero q
  have he : aeval (fun i : s => Ideal.Quotient.mk p (X i)) =
      (Ideal.Quotient.mkₐ K p).comp (rename (Subtype.val : s → σ)) := by
    ext i
    simp
  rw [he]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hq

theorem coordinateSplit_comap_coefficients_eq_bot_of_fractionField
    {K σ : Type*} [Field K] (s : Set σ) (p : Ideal (MvPolynomial σ K))
    (hs : AlgebraicIndependent K (fun i : s =>
      algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
        (Ideal.Quotient.mk p (X i)))) :
    (p.comap (coordinateSplit s).symm.toRingHom).comap
      (algebraMap (MvPolynomial s K) (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K))) = ⊥ := by
  apply coordinateSplit_comap_coefficients_eq_bot s p
  exact hs.of_comp (IsScalarTower.toAlgHom K (MvPolynomial σ K ⧸ p)
    (FractionRing (MvPolynomial σ K ⧸ p)))

def coordinateSplitLocalEquiv
    {K σ : Type*} [CommRing K] (s : Set σ) (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    Localization.AtPrime p ≃ₐ[K]
      Localization.AtPrime (p.comap (coordinateSplit s).symm.toRingHom) :=
  (Localization.localAlgEquiv (p.comap (coordinateSplit s).symm.toRingHom) p
    (coordinateSplit s).symm rfl).symm

theorem totalDegree_coordinateSplit_le
    {K σ : Type*} [CommSemiring K] (s : Set σ) (p : MvPolynomial σ K) :
    (coordinateSplit s p).totalDegree ≤ p.totalDegree := by
  classical
  let φ := (coordinateSplit (K := K) s).toRingHom
  have hX : ∀ i : σ, (φ (X i)).totalDegree ≤ 1 := by
    intro i
    by_cases hi : i ∈ s
    · change (coordinateSplit s (X (⟨i, hi⟩ : s))).totalDegree ≤ 1
      rw [coordinateSplit_X_mem s ⟨i, hi⟩]
      simp
    · change (coordinateSplit s (X (⟨i, hi⟩ : (sᶜ : Set σ)))).totalDegree ≤ 1
      rw [coordinateSplit_X_compl s ⟨i, hi⟩]
      cases subsingleton_or_nontrivial K
      · simp [Subsingleton.elim (X (⟨i, hi⟩ : (sᶜ : Set σ)) : MvPolynomial (sᶜ : Set σ) (MvPolynomial s K)) 0]
      · simp
  change (φ p).totalDegree ≤ p.totalDegree
  conv_lhs => rw [p.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  apply le_trans _ (le_totalDegree hd)
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod]
  calc
    _ ≤ (φ (C (p.coeff d))).totalDegree +
        (∑ i ∈ d.support, (φ (X i ^ d i)).totalDegree) :=
      (totalDegree_mul _ _).trans
        (Nat.add_le_add_left (totalDegree_finsetProd _ _) _)
    _ = ∑ i ∈ d.support, ((φ (X i)) ^ d i).totalDegree := by simp [φ]
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans
        (by simpa using Nat.mul_le_mul_left (d i) (hX i))
    _ = d.sum (fun _ e => e) := rfl

theorem totalDegree_localized_coordinateSplit_le
    {K σ : Type*} [Field K] (s : Set σ) (p : MvPolynomial σ K) :
    (MvPolynomial.map (algebraMap (MvPolynomial s K) (FractionRing (MvPolynomial s K)))
      (coordinateSplit s p)).totalDegree ≤ p.totalDegree := by
  exact (Finset.sup_mono (support_map_subset _ _)).trans (totalDegree_coordinateSplit_le s p)




def componentCoordinate {K σ : Type*} [Field K]
    (p : Ideal (MvPolynomial σ K)) (i : σ) :
    FractionRing (MvPolynomial σ K ⧸ p) :=
  algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
    (Ideal.Quotient.mk p (MvPolynomial.X i))

theorem aeval_componentCoordinate {K σ : Type*} [Field K]
    (p : Ideal (MvPolynomial σ K)) :
    MvPolynomial.aeval (componentCoordinate p) =
      (IsScalarTower.toAlgHom K (MvPolynomial σ K ⧸ p)
        (FractionRing (MvPolynomial σ K ⧸ p))).comp (Ideal.Quotient.mkₐ K p) := by
  ext i
  simp [componentCoordinate]

theorem ker_aeval_componentCoordinate {K σ : Type*} [Field K]
    (p : Ideal (MvPolynomial σ K)) :
    RingHom.ker (MvPolynomial.aeval (componentCoordinate p)).toRingHom = p := by
  rw [aeval_componentCoordinate]
  ext q
  change algebraMap (MvPolynomial σ K ⧸ p) (FractionRing (MvPolynomial σ K ⧸ p))
    (Ideal.Quotient.mk p q) = 0 ↔ q ∈ p
  rw [map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial σ K ⧸ p)
    (FractionRing (MvPolynomial σ K ⧸ p))), Ideal.Quotient.eq_zero_iff_mem]

theorem coordinateSplit_prime_eq_evaluation_kernel {K σ : Type*} [Field K]
    (s : Set σ) (p : Ideal (MvPolynomial σ K)) :
    p.comap (coordinateSplit s).symm.toRingHom =
      RingHom.ker (MvPolynomial.eval₂Hom
        (MvPolynomial.aeval (R := K) (fun i : s => componentCoordinate p i)).toRingHom
        (fun i : (sᶜ : Set σ) => componentCoordinate p i)) := by
  conv_lhs => rw [← ker_aeval_componentCoordinate p]
  rw [RingHom.comap_ker]
  congr 1
  apply RingHom.ext
  intro q
  exact aeval_coordinateSplit_symm s (componentCoordinate p) q

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem coordinateSplit_localized_prime_isMaximal {K σ : Type*} [Field K]
    (s : Set σ) (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (hs : IsTranscendenceBasis K (fun i : s => componentCoordinate p i)) :
    ((p.comap (coordinateSplit s).symm.toRingHom).map
      (algebraMap (MvPolynomial (sᶜ : Set σ) (MvPolynomial s K))
        (MvPolynomial (sᶜ : Set σ) (FractionRing (MvPolynomial s K))))).IsMaximal := by
  rw [coordinateSplit_prime_eq_evaluation_kernel]
  exact coordinateFraction_kernel_isMaximal hs
    (fun i : (sᶜ : Set σ) => componentCoordinate p i)

end WeightedTorusJets.Geometry

end

end SiegelZeros

end OAI
