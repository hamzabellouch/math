import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Structure.FiniteTypeFieldModelEquiv

namespace OAI

namespace SiegelZeros

section OriginalSourceGeometryOverlay
open Module CategoryTheory _root_.OAI.SiegelZeros.AlgebraicGeometry
open scoped BigOperators TensorProduct
noncomputable section
open scoped TensorProduct
open Module
namespace WeightedTorusJets.Geometry

theorem exists_independent_normal_finset_algebraMap {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (c : Fin 4 → K) (hc : c ≠ 0)
    (b : Module.Basis (Fin 3) K (LinearMap.ker (dotProductEquiv K (Fin 4) c)))
    (T : Submodule L (Fin 4 → L))
    (hT : T = ⊥ ∨ ¬ T ≤ LinearMap.ker
      (dotProductEquiv L (Fin 4) (algebraMap K L ∘ c))) :
    ∃ I : Finset (Fin 3), I.card = min (4 - Module.finrank L T) 3 ∧
      LinearIndepOn L (fun i => T.mkQ (algebraMap K L ∘ (b i : Fin 4 → K)))
        (I : Set (Fin 3)) := by
  obtain ⟨bL, hbL⟩ := exists_basis_ker_dotProduct_algebraMap (L := L) c hc b
  let ωL := dotProductEquiv L (Fin 4) (algebraMap K L ∘ c)
  have hd : Module.finrank L (LinearMap.ker ωL) = 3 := by
    simpa using Module.finrank_eq_card_basis bL
  have hωL : ωL ≠ 0 := by
    intro hzero
    rw [hzero, LinearMap.ker_zero, finrank_top, Module.finrank_pi,
      Fintype.card_fin] at hd
    omega
  obtain ⟨I, hI, hind⟩ := exists_independent_normal_finset ωL hωL (by simp) T hT bL
  refine ⟨I, hI, ?_⟩
  simpa only [hbL] using hind

end WeightedTorusJets.Geometry

open scoped BigOperators

namespace WeightedTorusJets.Geometry
attribute [local instance] Ideal.Quotient.field

theorem cotangent_finrank_add_logarithmic_tangent_finrank
    {K S : Type*} [Field K] [PerfectField K] [CommRing S]
    [Algebra K S] [Algebra (MvPolynomial (Fin 4) K) S]
    [IsScalarTower K (MvPolynomial (Fin 4) K) S]
    (M : Submonoid (MvPolynomial (Fin 4) K)) [IsLocalization M S]
    (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : Fin 4, IsUnit (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i))) :
    Module.finrank (S ⧸ I) I.Cotangent +
      Module.finrank (S ⧸ I) (LinearMap.range (logarithmicTangentMap (k := K)
        (fun i : Fin 4 => Ideal.Quotient.mk I
          (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i))))) = 4 := by
  have : Algebra.FormallyEtale (MvPolynomial (Fin 4) K) S :=
    Algebra.FormallyEtale.of_isLocalization M
  have : Algebra.EssFiniteType (MvPolynomial (Fin 4) K) S :=
    Algebra.EssFiniteType.of_isLocalization S M
  have : Algebra.EssFiniteType K S := Algebra.EssFiniteType.comp K (MvPolynomial (Fin 4) K) S
  let T := LinearMap.range (logarithmicTangentMap (k := K)
    (fun i : Fin 4 => Ideal.Quotient.mk I
      (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i))))
  have he := (coordinateNormalEquivCotangentDual I hx).finrank_eq
  rw [Subspace.dual_finrank_eq] at he
  rw [← he]
  simpa only [Module.finrank_pi, Fintype.card_fin] using T.finrank_quotient_add_finrank

theorem exists_selected_independent_normal_coordinates
    {K S : Type*} [Field K] [PerfectField K] [CommRing S]
    [Algebra K S] [Algebra (MvPolynomial (Fin 4) K) S]
    [IsScalarTower K (MvPolynomial (Fin 4) K) S]
    (M : Submonoid (MvPolynomial (Fin 4) K)) [IsLocalization M S]
    (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : Fin 4, IsUnit (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i)))
    (c : Fin 4 → K) (hc : c ≠ 0)
    (b : Module.Basis (Fin 3) K (LinearMap.ker (dotProductEquiv K (Fin 4) c)))
    (hform : Module.finrank (S ⧸ I) I.Cotangent ≤ 3 →
      logarithmicForm c (fun i : Fin 4 => Ideal.Quotient.mk I
        (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i))) ≠ 0) :
    ∃ J : Finset (Fin 3), J.card = min (Module.finrank (S ⧸ I) I.Cotangent) 3 ∧
      LinearIndependent (S ⧸ I) (fun j : J =>
        (LinearMap.range (logarithmicTangentMap (k := K) (fun i : Fin 4 =>
          Ideal.Quotient.mk I (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i))))).mkQ
          (algebraMap K (S ⧸ I) ∘ (b j : Fin 4 → K))) := by
  let f (i : Fin 4) := Ideal.Quotient.mk I
    (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i))
  let T := LinearMap.range (logarithmicTangentMap (k := K) f)
  have hdim : Module.finrank (S ⧸ I) I.Cotangent + Module.finrank (S ⧸ I) T = 4 :=
    cotangent_finrank_add_logarithmic_tangent_finrank M I hx
  have hω : logarithmicLinearForm (F := S ⧸ I) c =
      dotProductEquiv (S ⧸ I) (Fin 4) (algebraMap K (S ⧸ I) ∘ c) := by
    ext v
    simp [logarithmicLinearForm_apply, dotProduct, Function.comp_def]
  have hT : T = ⊥ ∨ ¬ T ≤ LinearMap.ker
      (dotProductEquiv (S ⧸ I) (Fin 4) (algebraMap K (S ⧸ I) ∘ c)) := by
    by_cases hh : Module.finrank (S ⧸ I) I.Cotangent ≤ 3
    · exact Or.inr (hω ▸ (logarithmicForm_ne_zero_iff_tangent_not_le c f).mp (hform hh))
    · exact Or.inl (Submodule.finrank_eq_zero.mp (by omega))
  obtain ⟨J, hJ, hind⟩ := exists_independent_normal_finset_algebraMap c hc b T hT
  exact ⟨J, hJ.trans (by congr 1; omega), hind⟩

theorem coordinateNormal_invariant_functional_eq
    {K S : Type*} [Field K] [PerfectField K] [CommRing S]
    [Algebra K S] [Algebra (MvPolynomial (Fin 4) K) S]
    [IsScalarTower K (MvPolynomial (Fin 4) K) S]
    [Algebra.FormallyEtale (MvPolynomial (Fin 4) K) S] [Algebra.EssFiniteType K S]
    (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : Fin 4, IsUnit (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i)))
    (D : Derivation K S S) (v : Fin 4 → K)
    (hD : ∀ i, D (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i)) =
      algebraMap K S (v i) * algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i)) :
    coordinateNormalEquivCotangentDual I hx (Submodule.Quotient.mk (algebraMap K (S ⧸ I) ∘ v)) =
      derivationCotangentResidue D I := by
  ext x
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  exact coordinateNormal_invariant_pairing I hx D (fun i => algebraMap K S (v i)) hD x

theorem exists_selected_independent_conormal_derivations
    {K S : Type*} [Field K] [PerfectField K] [CommRing S]
    [Algebra K S] [Algebra (MvPolynomial (Fin 4) K) S]
    [IsScalarTower K (MvPolynomial (Fin 4) K) S]
    (M : Submonoid (MvPolynomial (Fin 4) K)) [IsLocalization M S]
    (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : Fin 4, IsUnit (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i)))
    (c : Fin 4 → K) (hc : c ≠ 0)
    (b : Module.Basis (Fin 3) K (LinearMap.ker (dotProductEquiv K (Fin 4) c)))
    (hform : Module.finrank (S ⧸ I) I.Cotangent ≤ 3 →
      logarithmicForm c (fun i : Fin 4 => Ideal.Quotient.mk I
        (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i))) ≠ 0) :
    ∃ J : Finset (Fin 3), J.card = min (Module.finrank (S ⧸ I) I.Cotangent) 3 ∧
      LinearIndependent (S ⧸ I) (fun j : J => derivationCotangentResidue
        (localizeDerivation M (invariantDerivation (b j : Fin 4 → K))) I) := by
  have : Algebra.FormallyEtale (MvPolynomial (Fin 4) K) S :=
    Algebra.FormallyEtale.of_isLocalization M
  have : Algebra.EssFiniteType (MvPolynomial (Fin 4) K) S :=
    Algebra.EssFiniteType.of_isLocalization S M
  have : Algebra.EssFiniteType K S := Algebra.EssFiniteType.comp K (MvPolynomial (Fin 4) K) S
  obtain ⟨J, hJ, hind⟩ := exists_selected_independent_normal_coordinates M I hx c hc b hform
  refine ⟨J, hJ, ?_⟩
  let e := coordinateNormalEquivCotangentDual I hx
  have he (j : J) : e (Submodule.Quotient.mk (algebraMap K (S ⧸ I) ∘ (b j : Fin 4 → K))) =
      derivationCotangentResidue
        (localizeDerivation M (invariantDerivation (b j : Fin 4 → K))) I :=
    coordinateNormal_invariant_functional_eq I hx
      (localizeDerivation M (invariantDerivation (b j : Fin 4 → K))) (b j : Fin 4 → K)
      (fun i => localize_invariantDerivation_X M (b j : Fin 4 → K) i)
  have hi := hind.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  change LinearIndependent (S ⧸ I) (fun j : J =>
    e (Submodule.Quotient.mk (algebraMap K (S ⧸ I) ∘ (b j : Fin 4 → K)))) at hi
  have hfamily := funext he
  rwa [hfamily] at hi

end WeightedTorusJets.Geometry


namespace WeightedTorusJets.Geometry
attribute [local instance] Ideal.Quotient.field

theorem local_logarithmicForm_ne_zero_of_cotangent_le_three
    {K S : Type*} [Field K] [CharZero K] [IsAlgClosed K] [CommRing S]
    [Algebra K S] [Algebra (MvPolynomial (Fin 4) K) S]
    [IsScalarTower K (MvPolynomial (Fin 4) K) S]
    (M : Submonoid (MvPolynomial (Fin 4) K)) [IsLocalization M S]
    (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : Fin 4, IsUnit (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i)))
    (c : Fin 4 → K) (hc : LinearIndependent ℚ c)
    (hdim : Module.finrank (S ⧸ I) I.Cotangent ≤ 3) :
    logarithmicForm c (fun i : Fin 4 => Ideal.Quotient.mk I
      (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i))) ≠ 0 := by
  have : Algebra.EssFiniteType (MvPolynomial (Fin 4) K) S :=
    Algebra.EssFiniteType.of_isLocalization S M
  have : Algebra.EssFiniteType K S := Algebra.EssFiniteType.comp K (MvPolynomial (Fin 4) K) S
  let f (i : Fin 4) := Ideal.Quotient.mk I
    (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i))
  intro hform
  have hf (i : Fin 4) : f i ≠ 0 := ((hx i).map (Ideal.Quotient.mk I)).ne_zero
  have halg := isAlgebraic_of_logarithmicForm_eq_zero c hc f hf hform
  have hT : LinearMap.range (logarithmicTangentMap (k := K) f) = ⊥ := by
    apply LinearMap.range_eq_bot.mpr
    ext D i
    obtain ⟨a, ha⟩ := (halg i).isIntegral.mem_range_algebraMap_of_minpoly_splits
      (K := K) (by simpa using IsAlgClosed.splits (minpoly K (f i)))
    change (f i)⁻¹ * D (f i) = 0
    rw [← ha, D.map_algebraMap, mul_zero]
  have hd := cotangent_finrank_add_logarithmic_tangent_finrank M I hx
  change Module.finrank (S ⧸ I) I.Cotangent +
    Module.finrank (S ⧸ I) (LinearMap.range (logarithmicTangentMap (k := K) f)) = 4 at hd
  rw [hT, finrank_bot] at hd
  omega

theorem exists_selected_independent_conormal_derivations_atPrime
    {K S : Type*} [Field K] [CharZero K] [IsAlgClosed K] [CommRing S] [IsLocalRing S]
    [Algebra K S] [Algebra (MvPolynomial (Fin 4) K) S]
    [IsScalarTower K (MvPolynomial (Fin 4) K) S]
    (p : Ideal (MvPolynomial (Fin 4) K)) [p.IsPrime] [IsLocalization.AtPrime S p]
    (c : Fin 4 → K) (hc : LinearIndependent ℚ c)
    (b : Module.Basis (Fin 3) K (LinearMap.ker (dotProductEquiv K (Fin 4) c)))
    (hX : ∀ i : Fin 4, MvPolynomial.X i ∉ p) :
    ∃ J : Finset (Fin 3),
      J.card = min (Module.finrank (S ⧸ IsLocalRing.maximalIdeal S) (IsLocalRing.maximalIdeal S).Cotangent) 3 ∧
      LinearIndependent (S ⧸ IsLocalRing.maximalIdeal S) (fun j : J => derivationCotangentResidue
        (localizeDerivation p.primeCompl (invariantDerivation (b j : Fin 4 → K)))
          (IsLocalRing.maximalIdeal S)) := by
  have hx (i : Fin 4) : IsUnit (algebraMap (MvPolynomial (Fin 4) K) S (MvPolynomial.X i)) :=
    IsLocalization.map_units S (⟨MvPolynomial.X i, hX i⟩ : p.primeCompl)
  have hc0 : c ≠ 0 := by
    intro hzero
    exact hc.ne_zero (0 : Fin 4) (congrFun hzero 0)
  apply exists_selected_independent_conormal_derivations p.primeCompl
    (IsLocalRing.maximalIdeal S) hx c hc0 b
  intro hdim
  exact local_logarithmicForm_ne_zero_of_cotangent_le_three p.primeCompl
    (IsLocalRing.maximalIdeal S) hx c hc hdim

theorem exists_selected_first_order_taylor_parameters_atPrime
    {K S : Type*} [Field K] [CharZero K] [IsAlgClosed K] [CommRing S] [IsLocalRing S]
    [Algebra K S] [Algebra (MvPolynomial (Fin 4) K) S]
    [IsScalarTower K (MvPolynomial (Fin 4) K) S]
    (p : Ideal (MvPolynomial (Fin 4) K)) [p.IsPrime] [IsLocalization.AtPrime S p]
    (c : Fin 4 → K) (hc : LinearIndependent ℚ c)
    (b : Module.Basis (Fin 3) K (LinearMap.ker (dotProductEquiv K (Fin 4) c)))
    (hX : ∀ i : Fin 4, MvPolynomial.X i ∉ p) :
    ∃ J : Finset (Fin 3),
      J.card = min (Module.finrank (S ⧸ IsLocalRing.maximalIdeal S) (IsLocalRing.maximalIdeal S).Cotangent) 3 ∧
      ∀ a : J → S ⧸ IsLocalRing.maximalIdeal S, ∃ x : IsLocalRing.maximalIdeal S,
        ∀ j : J, Ideal.Quotient.mk (IsLocalRing.maximalIdeal S)
          (localizeDerivation p.primeCompl (invariantDerivation (b j : Fin 4 → K)) x) = a j := by
  obtain ⟨J, hJ, hind⟩ := exists_selected_independent_conormal_derivations_atPrime (S := S) p c hc b hX
  exact ⟨J, hJ, exists_ideal_element_with_derivatives (IsLocalRing.maximalIdeal S)
    (fun j : J => localizeDerivation p.primeCompl (invariantDerivation (b j : Fin 4 → K))) hind⟩

end WeightedTorusJets.Geometry

end
end OriginalSourceGeometryOverlay


open scoped BigOperators

namespace WeightedTorusJets.Geometry

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

theorem invariantDerivation_commute (c d : ι → R) :
    Function.Commute (invariantDerivation c) (invariantDerivation d) := by
  intro f
  induction f using MvPolynomial.induction_on' with
  | monomial m r =>
      simp only [invariantDerivation_monomial, Derivation.map_smul, smul_smul]
      rw [mul_comm]
  | add f g hf hg => simp only [map_add, hf, hg]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

omit [Algebra R S] [IsScalarTower R S T] in
theorem localization_derivation_ext (M : Submonoid S) [IsLocalization M T]
    {D E : Derivation R T T}
    (h : ∀ s : S, D (algebraMap S T s) = E (algebraMap S T s)) : D = E := by
  apply Derivation.ext
  intro t
  obtain ⟨s, m, rfl⟩ := IsLocalization.exists_mk'_eq M t
  have hd := D.leibniz (IsLocalization.mk' T s m) (algebraMap S T m)
  have he := E.leibniz (IsLocalization.mk' T s m) (algebraMap S T m)
  rw [IsLocalization.mk'_spec, h] at hd
  rw [IsLocalization.mk'_spec] at he
  simp only [smul_eq_mul, h] at hd he
  have heq : algebraMap S T (m : S) * D (IsLocalization.mk' T s m) =
      algebraMap S T (m : S) * E (IsLocalization.mk' T s m) := by
    exact add_left_cancel (hd.symm.trans he)
  exact (IsLocalization.map_units T m).mul_left_cancel heq

theorem iterate_localizeDerivation_algebraMap (M : Submonoid S) [IsLocalization M T]
    (D : Derivation R S S) (n : ℕ) (s : S) :
    (localizeDerivation M D)^[n] (algebraMap S T s) = algebraMap S T (D^[n] s) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [Function.iterate_succ_apply', hn, localizeDerivation_algebraMap,
      Function.iterate_succ_apply']

theorem localizeDerivation_commute (M : Submonoid S) [IsLocalization M T]
    (D E : Derivation R S S) (h : Function.Commute D E) :
    Function.Commute (localizeDerivation M D : T → T) (localizeDerivation M E) := by
  have hzero : ⁅localizeDerivation (T := T) M D, localizeDerivation (T := T) M E⁆ =
      (0 : Derivation R T T) := by
    apply localization_derivation_ext M
    intro s
    simp only [Derivation.commutator_apply, localizeDerivation_algebraMap,
      Derivation.zero_apply]
    rw [h s, sub_self]
  intro t
  exact sub_eq_zero.mp (by
    simpa only [Derivation.commutator_apply, Derivation.zero_apply] using
      congrArg (fun F : Derivation R T T => F t) hzero)

theorem mixed_localizeDerivation_algebraMap (M : Submonoid S) [IsLocalization M T]
    (D : Fin 3 → Derivation R S S) (a : Fin 3 → ℕ) (s : S) :
    ((localizeDerivation M (D 0)).toLinearMap ^ a 0)
      (((localizeDerivation M (D 1)).toLinearMap ^ a 1)
        (((localizeDerivation M (D 2)).toLinearMap ^ a 2) (algebraMap S T s))) =
    algebraMap S T (((D 0).toLinearMap ^ a 0)
      (((D 1).toLinearMap ^ a 1) (((D 2).toLinearMap ^ a 2) s))) := by
  simp only [Module.End.pow_apply, Derivation.coeFn_coe,
    iterate_localizeDerivation_algebraMap]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {K : Type*} [Field K]

theorem torus_algebraMap_injective :
    Function.Injective (algebraMap (MvPolynomial (Fin 4) K)
      (Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)))) := by
  have ht : (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ MvPolynomial.X_ne_zero i
  exact IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors ht)

theorem torus_polynomial_ne_zero {F : MvPolynomial (Fin 4) K} (hF : F ≠ 0) :
    algebraMap (MvPolynomial (Fin 4) K)
      (Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K))) F ≠ 0 := by
  exact fun h ↦ hF (torus_algebraMap_injective (h.trans (map_zero _).symm))

theorem torus_coordinate_isUnit (i : Fin 4) :
    IsUnit (algebraMap (MvPolynomial (Fin 4) K)
      (Localization.Away (∏ j : Fin 4, (MvPolynomial.X j : MvPolynomial (Fin 4) K)))
      (MvPolynomial.X i)) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (∏ j : Fin 4, (MvPolynomial.X j : MvPolynomial (Fin 4) K)))
    (∏ j : Fin 4, (MvPolynomial.X j : MvPolynomial (Fin 4) K))
  rw [map_prod] at h
  exact IsUnit.prod_univ_iff.mp h i

end WeightedTorusJets.Geometry


namespace WeightedTorusJets.Geometry

variable {R : Type*} [CommRing R] (I p : Ideal R) [p.IsPrime]

theorem component_local_radical (hp : p ∈ I.minimalPrimes) :
    (I.map (algebraMap R (Localization.AtPrime p))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
  rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime p) p I hp,
    Localization.AtPrime.map_eq_maximalIdeal]

theorem component_local_primary (hp : p ∈ I.minimalPrimes) :
    (I.map (algebraMap R (Localization.AtPrime p))).IsPrimary := by
  apply Ideal.isPrimary_of_isMaximal_radical
  rw [component_local_radical I p hp]
  infer_instance

theorem component_local_contains_maximal_pow [IsNoetherianRing R]
    (hp : p ∈ I.minimalPrimes) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal (Localization.AtPrime p) ^ n ≤
      I.map (algebraMap R (Localization.AtPrime p)) := by
  have h := (I.map (algebraMap R (Localization.AtPrime p))).exists_radical_pow_le_of_fg
    (Ideal.fg_of_isNoetherianRing _)
  rwa [component_local_radical I p hp] at h

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

noncomputable def torusEvalOne {K : Type*} [CommSemiring K] :
    Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)) →+* K :=
  IsLocalization.Away.lift
    (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K))
    (g := MvPolynomial.eval (fun _ ↦ (1 : K))) (by simp [map_prod])

@[simp] theorem torusEvalOne_algebraMap {K : Type*} [CommSemiring K]
    (F : MvPolynomial (Fin 4) K) :
    torusEvalOne (algebraMap (MvPolynomial (Fin 4) K)
      (Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K))) F) =
        MvPolynomial.eval (fun _ ↦ 1) F := by
  simp [torusEvalOne]

noncomputable def torusIdentityPoint {K : Type*} [Field K] :
    PrimeSpectrum
      (Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K))) :=
  ⟨RingHom.ker torusEvalOne, RingHom.ker_isPrime _⟩



theorem rectangleJetIdeal_mono {ι R : Type*} [CommRing R]
    (jet : (ι → ℕ) → R) (t : ι → ℕ) : Monotone (rectangleJetIdeal jet t) := by
  intro b c hbc
  apply Ideal.span_mono
  exact Set.image_mono fun a ha j ↦ (ha j).trans (Nat.mul_le_mul_right (t j) hbc)

theorem rectangleJetIdeal_zero {ι R : Type*} [CommRing R]
    (jet : (ι → ℕ) → R) (t : ι → ℕ) :
    rectangleJetIdeal jet t 0 = Ideal.span {jet 0} := by
  unfold rectangleJetIdeal
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, zero_mul, Nat.le_zero_eq,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact congrArg jet (funext ha)
  · rintro rfl
    exact ⟨0, fun _ ↦ rfl, rfl⟩

theorem rectangleJetZeroLocus_antitone {ι R : Type*} [CommRing R]
    (jet : (ι → ℕ) → R) (t : ι → ℕ) :
    Antitone (fun b ↦ PrimeSpectrum.zeroLocus (rectangleJetIdeal jet t b : Set R)) :=
  fun _ _ h ↦ PrimeSpectrum.zeroLocus_anti_mono_ideal (rectangleJetIdeal_mono jet t h)

theorem rectangleJetIdeal_le_ker {ι R S : Type*} [CommRing R] [CommRing S]
    (jet : (ι → ℕ) → R) (t : ι → ℕ) (φ : R →+* S) {b c : ℕ}
    (hbc : b ≤ c) (hvanish : ∀ a, (∀ j, a j ≤ c * t j) → φ (jet a) = 0) :
    rectangleJetIdeal jet t b ≤ RingHom.ker φ := by
  apply Ideal.span_le.mpr
  rintro _ ⟨a, ha, rfl⟩
  exact hvanish a fun j ↦ (ha j).trans (Nat.mul_le_mul_right (t j) hbc)

theorem exists_consecutive_eq_of_dimension_bound (d : ℕ → ℕ) (n : ℕ)
    (hd : ∀ b, b ≤ n → d (b + 1) ≤ d b) (hbound : d 0 ≤ n) :
    ∃ b, b ≤ n ∧ d b = d (b + 1) := by
  by_contra! h
  have hdecrease : ∀ b ≤ n, d (b + 1) < d b := by
    intro b hb
    exact lt_of_le_of_ne (hd b hb) (Ne.symm (h b hb))
  have hsteps : ∀ b ≤ n + 1, d b + b ≤ d 0 := by
    intro b
    induction b with
    | zero => simp
    | succ b ih =>
      intro hb
      have hi := ih (by omega)
      have hj := hdecrease b (by omega)
      omega
  have := hsteps (n + 1) le_rfl
  omega

theorem isIrreducible_subtype_preimage {X : Type*} [TopologicalSpace X]
    {S Z : Set X} (hS : IsIrreducible S) (hSZ : S ⊆ Z) :
    IsIrreducible ((Subtype.val : Z → X) ⁻¹' S) := by
  let := Subtype.irreducibleSpace hS
  let f : S → Z := fun s ↦ ⟨s, hSZ s.2⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hi := (IrreducibleSpace.isIrreducible_univ S).image f hf.continuousOn
  convert hi using 1
  ext z
  constructor
  · intro hz
    exact ⟨⟨z, hz⟩, Set.mem_univ _, Subtype.ext rfl⟩
  · rintro ⟨y, _, rfl⟩
    exact y.2

def irreducibleClosedSubtypeEmbedding {X : Type*} [TopologicalSpace X] (Z : Set X) :
    {V : TopologicalSpace.IrreducibleCloseds X // (V : Set X) ⊆ Z} ↪o
      TopologicalSpace.IrreducibleCloseds Z :=
  OrderEmbedding.ofMapLEIff
    (fun V ↦ ⟨Subtype.val ⁻¹' (V.1 : Set X),
      isIrreducible_subtype_preimage V.1.isIrreducible V.2,
      V.1.isClosed.preimage continuous_subtype_val⟩)
    fun A _ ↦ ⟨fun h x hx ↦ h (show (⟨x, A.2 hx⟩ : Z) ∈
      Subtype.val ⁻¹' (A.1 : Set X) from hx), fun h _ hx ↦ h hx⟩

theorem local_irreducible_dimension_nat {X : Type*} [TopologicalSpace X]
    (x : X) (Z : Set X) (hx : x ∈ Z) (hZ : IsClosed Z) (n : ℕ)
    (hdim : topologicalKrullDim Z ≤ n) :
    ∃ d ≤ n, Order.krullDim
      {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z} = d := by
  let A := {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z}
  let e : A ↪o {V : TopologicalSpace.IrreducibleCloseds X // (V : Set X) ⊆ Z} :=
    Subtype.orderEmbedding (fun _ hV ↦ hV.2)
  have hb : Order.krullDim A ≤ n :=
    (Order.krullDim_le_of_orderEmbedding (e.trans (irreducibleClosedSubtypeEmbedding Z))).trans hdim
  let : Nonempty A := ⟨⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩,
    subset_closure (Set.mem_singleton x),
    closure_minimal (Set.singleton_subset_iff.mpr hx) hZ⟩⟩
  let : FiniteDimensionalOrder A :=
    Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mpr
      ⟨Order.krullDim_ne_bot_iff.mpr inferInstance,
        ne_top_of_le_ne_top (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top n)).ne hb⟩
  have heq := Order.krullDim_eq_length_of_finiteDimensionalOrder (α := A)
  refine ⟨(LTSeries.longestOf A).length, ?_, heq⟩
  rw [heq] at hb
  exact_mod_cast hb

theorem localization_ringKrullDim_le {R S : Type*} [CommRing R] [CommRing S]
    (M : Submonoid R) [Algebra R S] [IsLocalization M S] :
    ringKrullDim S ≤ ringKrullDim R := by
  rw [ringKrullDim, Order.krullDim_eq_of_orderIso (IsLocalization.primeSpectrumOrderIso M S)]
  exact Order.krullDim_le_of_orderEmbedding (OrderEmbedding.subtype _)

theorem hypersurface_ringKrullDim_le {R : Type*} [CommRing R] [IsDomain R]
    {F : R} (hF : F ≠ 0) {n : ℕ} (hdim : ringKrullDim R ≤ n + 1) :
    ringKrullDim (R ⧸ Ideal.span {F}) ≤ n := by
  exact ENat.WithBot.add_le_add_one_right_iff.mp
    ((ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (mem_nonZeroDivisors_of_ne_zero hF)).trans hdim)

theorem four_variable_localization_ringKrullDim_le {k S : Type*} [Field k] [CommRing S]
    (M : Submonoid (MvPolynomial (Fin 4) k)) [Algebra (MvPolynomial (Fin 4) k) S]
    [IsLocalization M S] : ringKrullDim S ≤ 4 := by
  have hdim := localization_ringKrullDim_le (S := S) M
  simpa [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field] using hdim

theorem vanishingIdeal_isMinimalPrime_of_maximal {R : Type*} [CommRing R]
    (I : Ideal R) (V : Set (PrimeSpectrum R))
    (hV : Maximal (fun S ↦ IsIrreducible S ∧ S ⊆ PrimeSpectrum.zeroLocus (I : Set R)) V) :
    I.IsMinimalPrime (PrimeSpectrum.vanishingIdeal V) := by
  refine ⟨⟨PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hV.1.1,
    (PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal V I).mp hV.1.2⟩, ?_⟩
  intro q hq hqV
  have hVq : V ⊆ PrimeSpectrum.zeroLocus (q : Set R) :=
    (PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal V q).mpr hqV
  have hqV' : PrimeSpectrum.zeroLocus (q : Set R) ⊆ V :=
    hV.2 ⟨(PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical q hq.1.isRadical).mpr hq.1,
      PrimeSpectrum.zeroLocus_anti_mono_ideal hq.2⟩ hVq
  have h := PrimeSpectrum.vanishingIdeal_anti_mono hqV'
  simpa only [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hq.1.isRadical.radical] using h

theorem exists_shared_maximal_of_krullDim_eq_with_height {α β : Type*}
    [PartialOrder α] [PartialOrder β] (e : β ↪o α) (n : ℕ)
    (hα : Order.krullDim α = n) (hβ : Order.krullDim β = n) :
    ∃ b : β, IsMax b ∧ IsMax (e b) ∧ Order.height b = n ∧ Order.height (e b) = n := by
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp (le_of_eq hβ.symm)
  let q := p.map e e.strictMono
  have hmax : IsMax (e p.last) := by
    intro a ha
    by_contra hnot
    have hlt : q.last < a := lt_of_le_not_ge ha hnot
    have hlength := Order.LTSeries.length_le_krullDim (q.snoc a hlt)
    have hn : (n + 1 : WithBot ℕ∞) ≤ n := by
      simpa [q, hp, hα] using hlength
    norm_cast at hn
    omega
  refine ⟨p.last, fun b hb ↦ e.le_iff_le.mp (hmax (e.monotone hb)), hmax, ?_, ?_⟩
  · apply le_antisymm
    · have hd := Order.height_le_krullDim p.last
      rw [hβ] at hd
      exact_mod_cast hd
    · simpa [hp] using Order.length_le_height_last (p := p)
  · apply le_antisymm
    · have hd := Order.height_le_krullDim (e p.last)
      rw [hα] at hd
      exact_mod_cast hd
    · simpa [q, hp] using Order.length_le_height_last (p := q)

theorem local_irreducible_dimension_eq_order_height
    {X : Type*} [TopologicalSpace X] (x : X) (Z : Set X)
    (V : {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z}) :
    Order.krullDim
      {W : TopologicalSpace.IrreducibleCloseds X // x ∈ W ∧ (W : Set X) ⊆ V.1} =
      (Order.height V : WithBot ℕ∞) := by
  let e : {W : TopologicalSpace.IrreducibleCloseds X // x ∈ W ∧ (W : Set X) ⊆ V.1} ≃o
      Set.Iic V :=
    { toFun := fun W ↦ ⟨⟨W.1, W.2.1, W.2.2.trans V.2.2⟩, W.2.2⟩
      invFun := fun W ↦ ⟨W.1.1, W.1.2.1, W.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_rel_iff' := Iff.rfl }
  exact (Order.krullDim_eq_of_orderIso e).trans (Order.height_eq_krullDim_Iic V).symm

theorem exists_shared_component_of_full_local_dimension
    {X : Type*} [TopologicalSpace X] (x : X) (Z₁ Z₂ : Set X)
    (hZ₁ : IsClosed Z₁) (hZ₂Z₁ : Z₂ ⊆ Z₁) (n : ℕ)
    (hd₁ : Order.krullDim
      {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z₁} = n)
    (hd₂ : Order.krullDim
      {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z₂} = n) :
    ∃ V : Set X, x ∈ V ∧ V ⊆ Z₂ ∧
      Maximal (fun S ↦ IsIrreducible S ∧ S ⊆ Z₁) V ∧
      Maximal (fun S ↦ IsIrreducible S ∧ S ⊆ Z₂) V ∧
      Order.krullDim
        {W : TopologicalSpace.IrreducibleCloseds X // x ∈ W ∧ (W : Set X) ⊆ V} = n := by
  let e : {V : TopologicalSpace.IrreducibleCloseds X //
      x ∈ V ∧ (V : Set X) ⊆ Z₂} ↪o
      {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z₁} :=
    Subtype.orderEmbedding (fun V hV ↦ ⟨hV.1, hV.2.trans hZ₂Z₁⟩)
  obtain ⟨V, _, hmax, hVheight, _⟩ :=
    exists_shared_maximal_of_krullDim_eq_with_height e n hd₁ hd₂
  have hm : Maximal (fun S : Set X ↦ IsIrreducible S ∧ S ⊆ Z₁) (V.1 : Set X) := by
    refine ⟨⟨V.1.isIrreducible, V.2.2.trans hZ₂Z₁⟩, ?_⟩
    intro S hS hVS
    let W : {W : TopologicalSpace.IrreducibleCloseds X //
        x ∈ W ∧ (W : Set X) ⊆ Z₁} :=
      ⟨⟨closure S, hS.1.closure, isClosed_closure⟩,
        subset_closure (hVS V.2.1), closure_minimal hS.2 hZ₁⟩
    have hVW : e V ≤ W := fun _ hy ↦ subset_closure (hVS hy)
    exact subset_closure.trans (hmax hVW)
  refine ⟨V.1, V.2.1, V.2.2, hm,
    ⟨⟨V.1.isIrreducible, V.2.2⟩,
      fun S hS hVS ↦ hm.2 ⟨hS.1, hS.2.trans hZ₂Z₁⟩ hVS⟩, ?_⟩
  rw [local_irreducible_dimension_eq_order_height x Z₂ V, hVheight]
  rfl

theorem exists_shared_component_of_dimension_three_full
    {X : Type*} [TopologicalSpace X] (x : X) (Z : ℕ → Set X)
    (hclosed : ∀ b ≤ 4, IsClosed (Z b)) (hnested : Antitone Z)
    (hx : x ∈ Z 4) (hdim : topologicalKrullDim (Z 0) ≤ 3) :
    ∃ b ≤ 3, ∃ n : ℕ, n ≤ 3 ∧ ∃ V : Set X,
      x ∈ V ∧ V ⊆ Z (b + 1) ∧
      Maximal (fun S ↦ IsIrreducible S ∧ S ⊆ Z b) V ∧
      Maximal (fun S ↦ IsIrreducible S ∧ S ⊆ Z (b + 1)) V ∧
      Order.krullDim
        {W : TopologicalSpace.IrreducibleCloseds X // x ∈ W ∧ (W : Set X) ⊆ Z b} = n ∧
      Order.krullDim
        {W : TopologicalSpace.IrreducibleCloseds X // x ∈ W ∧ (W : Set X) ⊆ Z (b + 1)} = n ∧
      Order.krullDim
        {W : TopologicalSpace.IrreducibleCloseds X // x ∈ W ∧ (W : Set X) ⊆ V} = n := by
  have hex : ∀ b, b ≤ 4 → ∃ d : ℕ, d ≤ 3 ∧ Order.krullDim
      {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z b} = d := by
    intro b hb
    apply local_irreducible_dimension_nat x (Z b) (hnested hb hx) (hclosed b hb) 3
    have he := (Topology.IsEmbedding.inclusion (hnested (Nat.zero_le b))).isInducing
    exact he.topologicalKrullDim_le.trans hdim
  let d (b : ℕ) : ℕ := if hb : b ≤ 4 then (hex b hb).choose else 0
  have hd : ∀ b, b ≤ 4 → Order.krullDim
      {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z b} = d b := by
    intro b hb
    simpa only [d, dite_eq_left hb] using (hex b hb).choose_spec.2
  have hdle : ∀ b, b ≤ 4 → d b ≤ 3 := by
    intro b hb
    simpa only [d, dite_eq_left hb] using (hex b hb).choose_spec.1
  have hmono : ∀ b, b ≤ 3 → d (b + 1) ≤ d b := by
    intro b hb
    let e : {V : TopologicalSpace.IrreducibleCloseds X //
        x ∈ V ∧ (V : Set X) ⊆ Z (b + 1)} ↪o
        {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z b} :=
      Subtype.orderEmbedding (fun V hV ↦ ⟨hV.1, hV.2.trans (hnested (Nat.le_succ b))⟩)
    have he := Order.krullDim_le_of_orderEmbedding e
    rw [hd b (by omega), hd (b + 1) (by omega)] at he
    exact_mod_cast he
  obtain ⟨b, hb, heq⟩ := exists_consecutive_eq_of_dimension_bound d 3 hmono (hdle 0 (by omega))
  have hdnext : Order.krullDim
      {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z (b + 1)} = d b := by
    rw [hd (b + 1) (by omega), heq]
  obtain ⟨V, hxV, hVZ, hm₁, hm₂, hVdim⟩ :=
    exists_shared_component_of_full_local_dimension x (Z b) (Z (b + 1))
      (hclosed b (by omega)) (hnested (Nat.le_succ b)) (d b) (hd b (by omega)) hdnext
  exact ⟨b, hb, d b, hdle b (by omega), V, hxV, hVZ, hm₁, hm₂,
    hd b (by omega), hdnext, hVdim⟩

theorem rectangleJets_have_shared_component_full
    {ι R : Type*} [CommRing R] [IsDomain R]
    (jet : (ι → ℕ) → R) (t : ι → ℕ) (p : PrimeSpectrum R)
    (hp : rectangleJetIdeal jet t 4 ≤ p.asIdeal) (hjet : jet 0 ≠ 0)
    (hdim : ringKrullDim R ≤ 4) :
    let Z := fun b ↦ PrimeSpectrum.zeroLocus (rectangleJetIdeal jet t b : Set R)
    ∃ b ≤ 3, ∃ n : ℕ, n ≤ 3 ∧ ∃ V : Set (PrimeSpectrum R),
      p ∈ V ∧ V ⊆ Z (b + 1) ∧
      Maximal (fun S ↦ IsIrreducible S ∧ S ⊆ Z b) V ∧
      Maximal (fun S ↦ IsIrreducible S ∧ S ⊆ Z (b + 1)) V ∧
      Order.krullDim
        {W : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) //
          p ∈ W ∧ (W : Set (PrimeSpectrum R)) ⊆ Z b} = n ∧
      Order.krullDim
        {W : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) //
          p ∈ W ∧ (W : Set (PrimeSpectrum R)) ⊆ Z (b + 1)} = n ∧
      Order.krullDim
        {W : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) //
          p ∈ W ∧ (W : Set (PrimeSpectrum R)) ⊆ V} = n := by
  apply exists_shared_component_of_dimension_three_full p
    (fun b ↦ PrimeSpectrum.zeroLocus (rectangleJetIdeal jet t b : Set R))
    (fun b _ ↦ PrimeSpectrum.isClosed_zeroLocus _)
    (rectangleJetZeroLocus_antitone jet t) hp
  calc
    topologicalKrullDim (PrimeSpectrum.zeroLocus (rectangleJetIdeal jet t 0 : Set R)) =
        Order.krullDim (TopologicalSpace.IrreducibleCloseds
          (PrimeSpectrum.zeroLocus (rectangleJetIdeal jet t 0 : Set R)))ᵒᵈ :=
      Order.krullDim_orderDual.symm
    _ = Order.krullDim (PrimeSpectrum.zeroLocus (rectangleJetIdeal jet t 0 : Set R)) :=
      (Order.krullDim_eq_of_orderIso
        (PrimeSpectrum.zeroLocusEquivIrreducibleCloseds
          (rectangleJetIdeal jet t 0 : Set R))).symm
    _ = ringKrullDim (R ⧸ rectangleJetIdeal jet t 0) := (ringKrullDim_quotient _).symm
    _ ≤ 3 := by
      rw [rectangleJetIdeal_zero]
      exact hypersurface_ringKrullDim_le hjet hdim

theorem rectangleJets_have_shared_minimal_prime {ι R : Type*} [CommRing R] [IsDomain R]
    (jet : (ι → ℕ) → R) (t : ι → ℕ) (p : PrimeSpectrum R)
    (hp : rectangleJetIdeal jet t 4 ≤ p.asIdeal) (hjet : jet 0 ≠ 0)
    (hdim : ringKrullDim R ≤ 4) :
    ∃ b ≤ 3, ∃ q : Ideal R, q ≤ p.asIdeal ∧
      (rectangleJetIdeal jet t b).IsMinimalPrime q ∧
      (rectangleJetIdeal jet t (b + 1)).IsMinimalPrime q := by
  obtain ⟨b, hb, _, _, V, hpV, _, hVb, hVb', _⟩ :=
    rectangleJets_have_shared_component_full jet t p hp hjet hdim
  refine ⟨b, hb, PrimeSpectrum.vanishingIdeal V, ?_,
    vanishingIdeal_isMinimalPrime_of_maximal _ V hVb,
    vanishingIdeal_isMinimalPrime_of_maximal _ V hVb'⟩
  simpa only [PrimeSpectrum.vanishingIdeal_singleton] using
    PrimeSpectrum.vanishingIdeal_anti_mono (Set.singleton_subset_iff.mpr hpV)

end WeightedTorusJets.Geometry

open scoped BigOperators


end SiegelZeros

end OAI
