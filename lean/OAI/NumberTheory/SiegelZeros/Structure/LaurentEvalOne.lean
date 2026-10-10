import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Intersection.TorusEvalOne
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.PolynomialLaurent

namespace OAI

namespace SiegelZeros

section

section
namespace WeightedTorusJets.Geometry

theorem prime_genericPoint_zeroLocus {R : Type*} [CommRing R] (q : PrimeSpectrum R) :
    IsGenericPoint q (PrimeSpectrum.zeroLocus (q.asIdeal : Set R)) :=
  PrimeSpectrum.closure_singleton q

theorem zeroLocus_maximal_of_isMinimalPrime {R : Type*} [CommRing R]
    (I : Ideal R) (q : PrimeSpectrum R) (hq : I.IsMinimalPrime q.asIdeal) :
    Maximal (fun V : Set (PrimeSpectrum R) => IsIrreducible V ∧
      V ⊆ PrimeSpectrum.zeroLocus (I : Set R))
      (PrimeSpectrum.zeroLocus (q.asIdeal : Set R)) := by
  refine ⟨⟨(prime_genericPoint_zeroLocus q).isIrreducible,
    PrimeSpectrum.zeroLocus_anti_mono_ideal hq.le⟩, ?_⟩
  intro V hV hqV
  have hp : (PrimeSpectrum.vanishingIdeal V).IsPrime :=
    PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hV.1
  have hIp : I ≤ PrimeSpectrum.vanishingIdeal V :=
    (PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal V I).mp hV.2
  have hpq : PrimeSpectrum.vanishingIdeal V ≤ q.asIdeal := by
    simpa only [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
      Ideal.IsPrime.radical] using PrimeSpectrum.vanishingIdeal_anti_mono hqV
  exact (PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal V q.asIdeal).mpr
    (hq.2 ⟨hp, hIp⟩ hpq)

theorem isClosed_of_maximal_irreducible_zeroLocus {R : Type*} [CommRing R]
    (I : Ideal R) (V : Set (PrimeSpectrum R))
    (hV : Maximal (fun W => IsIrreducible W ∧
      W ⊆ PrimeSpectrum.zeroLocus (I : Set R)) V) : IsClosed V := by
  apply isClosed_of_closure_subset
  exact hV.2 ⟨hV.1.1.closure,
    closure_minimal hV.1.2 (PrimeSpectrum.isClosed_zeroLocus _)⟩ subset_closure

theorem maximal_component_genericPoint {R : Type*} [CommRing R]
    (I : Ideal R) (V : Set (PrimeSpectrum R))
    (hV : Maximal (fun W => IsIrreducible W ∧
      W ⊆ PrimeSpectrum.zeroLocus (I : Set R)) V) :
    IsGenericPoint
      (⟨PrimeSpectrum.vanishingIdeal V,
        PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hV.1.1⟩ : PrimeSpectrum R) V := by
  rw [IsGenericPoint, PrimeSpectrum.closure_singleton,
    PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  exact (isClosed_of_maximal_irreducible_zeroLocus I V hV).closure_eq

theorem shared_minimal_prime_has_generic_component {R : Type*} [CommRing R]
    (I J : Ideal R) (q p : PrimeSpectrum R) (hqp : q.asIdeal ≤ p.asIdeal)
    (hI : I.IsMinimalPrime q.asIdeal) (hJ : J.IsMinimalPrime q.asIdeal) :
    ∃ V : Set (PrimeSpectrum R), p ∈ V ∧ IsGenericPoint q V ∧
      Maximal (fun W => IsIrreducible W ∧ W ⊆ PrimeSpectrum.zeroLocus (I : Set R)) V ∧
      Maximal (fun W => IsIrreducible W ∧ W ⊆ PrimeSpectrum.zeroLocus (J : Set R)) V :=
  ⟨PrimeSpectrum.zeroLocus (q.asIdeal : Set R), hqp,
    prime_genericPoint_zeroLocus q, zeroLocus_maximal_of_isMinimalPrime I q hI,
    zeroLocus_maximal_of_isMinimalPrime J q hJ⟩

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem zeroLocus_topologicalKrullDim {R : Type*} [CommRing R] (I : Ideal R) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set R)) = ringKrullDim (R ⧸ I) := by
  calc
    topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set R)) =
        Order.krullDim (TopologicalSpace.IrreducibleCloseds
          (PrimeSpectrum.zeroLocus (I : Set R)))ᵒᵈ := Order.krullDim_orderDual.symm
    _ = Order.krullDim (PrimeSpectrum.zeroLocus (I : Set R)) :=
      (Order.krullDim_eq_of_orderIso (PrimeSpectrum.zeroLocusEquivIrreducibleCloseds
        (I : Set R))).symm
    _ = ringKrullDim (R ⧸ I) := (ringKrullDim_quotient I).symm

theorem generic_component_topologicalKrullDim {R : Type*} [CommRing R]
    (q : PrimeSpectrum R) (V : Set (PrimeSpectrum R)) (hV : IsGenericPoint q V) :
    topologicalKrullDim V = ringKrullDim (R ⧸ q.asIdeal) := by
  rw [← hV, PrimeSpectrum.closure_singleton, zeroLocus_topologicalKrullDim]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open _root_.AlgebraicGeometry

variable {R : Type*} [CommRing R]

theorem spec_stalk_isLocalRing (p : PrimeSpectrum R) :
    IsLocalRing ((Spec.structureSheaf R).presheaf.stalk p) :=
  (StructureSheaf.stalkIso R p).toRingEquiv.isLocalRing

attribute [local instance] spec_stalk_isLocalRing

theorem spec_localization_stalk_regular [IsRegularRing R]
    (M : Submonoid R) (p : PrimeSpectrum (Localization M)) :
    IsRegularLocalRing ((Spec.structureSheaf (Localization M)).presheaf.stalk p) :=
  IsRegularLocalRing.of_ringEquiv
    ((IsLocalization.localizationLocalizationAtPrimeIsoLocalization M p.asIdeal).toRingEquiv.trans
      (StructureSheaf.stalkIso (Localization M) p).toRingEquiv)

theorem spec_stalk_component_radical (I : Ideal R) (p : PrimeSpectrum R)
    (hp : p.asIdeal ∈ I.minimalPrimes) :
    (I.map (algebraMap R ((Spec.structureSheaf R).presheaf.stalk p))).radical =
      IsLocalRing.maximalIdeal ((Spec.structureSheaf R).presheaf.stalk p) := by
  rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    ((Spec.structureSheaf R).presheaf.stalk p) p.asIdeal I hp,
    IsLocalization.AtPrime.map_eq_maximalIdeal]

theorem spec_stalk_component_primary (I : Ideal R) (p : PrimeSpectrum R)
    (hp : p.asIdeal ∈ I.minimalPrimes) :
    (I.map (algebraMap R ((Spec.structureSheaf R).presheaf.stalk p))).IsPrimary := by
  apply Ideal.isPrimary_of_isMaximal_radical
  rw [spec_stalk_component_radical I p hp]
  infer_instance

end WeightedTorusJets.Geometry
end

section
namespace WeightedTorusJets.Geometry

theorem torusEvalOne_unique {K : Type*} [CommSemiring K]
    (φ : Localization.Away
      (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)) →+* K)
    (hC : ∀ c, φ (algebraMap (MvPolynomial (Fin 4) K) _ (MvPolynomial.C c)) = c)
    (hX : ∀ i : Fin 4, φ (algebraMap (MvPolynomial (Fin 4) K) _ (MvPolynomial.X i)) = 1) :
    φ = torusEvalOne := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)))
  apply MvPolynomial.ringHom_ext
  · intro c
    simpa only [RingHom.comp_apply, torusEvalOne_algebraMap, MvPolynomial.eval_C] using hC c
  · intro i
    simpa only [RingHom.comp_apply, torusEvalOne_algebraMap, MvPolynomial.eval_X] using hX i

end WeightedTorusJets.Geometry
end

section

namespace WeightedTorusJets.Geometry

open scoped BigOperators

variable (K ι : Type*) [CommRing K]

local notation "P" => MvPolynomial ι K
local notation "G" => ι →₀ ℤ
local notation "A" => AddMonoidAlgebra K G
local notation "L" => Localization.Away (∏ i : ι, (MvPolynomial.X i : P))

variable [Fintype ι]

@[simp] theorem laurentEquivLocalization_symm_algebraMap (p : P) :
    (laurentEquivLocalization K ι).symm (algebraMap P L p) =
      polynomialToLaurent K ι p := by
  simp [laurentEquivLocalization, localizationToLaurent]

@[simp] theorem laurentEquivLocalization_polynomial (p : P) :
    laurentEquivLocalization K ι (polynomialToLaurent K ι p) = algebraMap P L p := by
  rw [← laurentEquivLocalization_symm_algebraMap, AlgEquiv.apply_symm_apply]

theorem laurentEquivLocalization_inverse_coordinate (i : ι) :
    laurentEquivLocalization K ι (AddMonoidAlgebra.single (Finsupp.single i (-1)) 1) =
      ((localizedCoordinateUnit K ι i)⁻¹ : Lˣ) := by
  simp [laurentEquivLocalization, laurentToLocalization]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable (K ι : Type*) [CommRing K]

noncomputable def laurentEvalOne : AddMonoidAlgebra K (ι →₀ ℤ) →ₐ[K] K :=
  AddMonoidAlgebra.lift K K (ι →₀ ℤ) 1

@[simp] theorem laurentEvalOne_polynomial (p : MvPolynomial ι K) :
    laurentEvalOne K ι (polynomialToLaurent K ι p) =
      MvPolynomial.eval (fun _ => 1) p := by
  simp [polynomialToLaurent, MvPolynomial.comp_aeval_apply, laurentEvalOne,
    MvPolynomial.aeval_eq_eval]

theorem laurentEvalOne_eq_torusEvalOne
    (p : AddMonoidAlgebra K (Fin 4 →₀ ℤ)) :
    laurentEvalOne K (Fin 4) p =
      torusEvalOne (laurentEquivLocalization K (Fin 4) p) := by
  let e := laurentEquivLocalization K (Fin 4)
  have h : (laurentEvalOne K (Fin 4)).toRingHom.comp e.symm.toRingHom = torusEvalOne := by
    apply torusEvalOne_unique <;> intro x <;> simp [e, laurentEvalOne]
  simpa using RingHom.congr_fun h (e p)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem laurent_identity_ideal_map (K : Type*) [Field K] :
    (RingHom.ker (laurentEvalOne K (Fin 4)).toRingHom).map
      (laurentEquivLocalization K (Fin 4)) =
      (torusIdentityPoint (K := K)).asIdeal := by
  let e := laurentEquivLocalization K (Fin 4)
  have h : (torusIdentityPoint (K := K)).asIdeal.comap e =
      RingHom.ker (laurentEvalOne K (Fin 4)).toRingHom := by
    ext a
    change torusEvalOne (e a) = 0 ↔ laurentEvalOne K (Fin 4) a = 0
    rw [laurentEvalOne_eq_torusEvalOne]
  rw [← h, Ideal.map_comap_eq_self_of_equiv]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable (K ι : Type*) [CommRing K] [Fintype ι]

noncomputable def laurentLocalRingEquivLocalization
    (I : Ideal (AddMonoidAlgebra K (ι →₀ ℤ))) [I.IsPrime] :
    Localization.AtPrime I ≃ₐ[K]
      Localization.AtPrime (I.map (laurentEquivLocalization K ι)) :=
  Localization.localAlgEquiv I _ (laurentEquivLocalization K ι)
    (I.comap_map_of_bijective _ (laurentEquivLocalization K ι).bijective).symm

@[simp] theorem laurentLocalRingEquivLocalization_algebraMap
    (I : Ideal (AddMonoidAlgebra K (ι →₀ ℤ))) [I.IsPrime]
    (a : AddMonoidAlgebra K (ι →₀ ℤ)) :
    laurentLocalRingEquivLocalization K ι I
      (algebraMap _ (Localization.AtPrime I) a) =
    algebraMap _ (Localization.AtPrime
      (I.map (laurentEquivLocalization K ι)))
      (laurentEquivLocalization K ι a) := by
  simp [laurentLocalRingEquivLocalization, Localization.localAlgHom]

end WeightedTorusJets.Geometry
end

section
section
namespace WeightedTorusJets.Geometry

theorem spectrum_local_irreducible_dimension_eq_localRing
    {R : Type*} [CommRing R] (p : PrimeSpectrum R) :
    Order.krullDim
      {V : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) // p ∈ V} =
      ringKrullDim (Localization.AtPrime p.asIdeal) := by
  let e := PrimeSpectrum.pointsEquivIrreducibleCloseds R
  have hmem (q : PrimeSpectrum R) :
      p ∈ (OrderDual.ofDual (e q) : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R)) ↔
        q ≤ p := by
    change p ∈ closure ({q} : Set (PrimeSpectrum R)) ↔ q ≤ p
    exact (PrimeSpectrum.le_iff_mem_closure q p).symm
  let f : (Set.Iic p)ᵒᵈ ≃o
      {V : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) // p ∈ V} :=
    { toFun := fun q ↦ ⟨OrderDual.ofDual (e q.1), (hmem q.1).mpr q.2⟩
      invFun := fun V ↦ ⟨e.symm (OrderDual.toDual V.1),
        (hmem (e.symm (OrderDual.toDual V.1))).mp
        (by simpa only [e.apply_symm_apply, OrderDual.ofDual_toDual] using V.2)⟩
      left_inv := fun q ↦ Subtype.ext (e.symm_apply_apply q.1)
      right_inv := fun V ↦ Subtype.ext (e.apply_symm_apply (OrderDual.toDual V.1))
      map_rel_iff' := e.le_iff_le }
  calc
    Order.krullDim
        {V : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) // p ∈ V} =
        Order.krullDim (Set.Iic p)ᵒᵈ := (Order.krullDim_eq_of_orderIso f).symm
    _ = Order.krullDim (Set.Iic p) := Order.krullDim_orderDual
    _ = (Order.height p : WithBot ℕ∞) := (Order.height_eq_krullDim_Iic p).symm
    _ = (p.asIdeal.height : WithBot ℕ∞) := by rw [PrimeSpectrum.height_eq_orderHeight]
    _ = ringKrullDim (Localization.AtPrime p.asIdeal) :=
      (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal _).symm

end WeightedTorusJets.Geometry

end

section
namespace WeightedTorusJets.Geometry

theorem local_irreducible_closed_subspace_dimension_eq
    {X : Type*} [TopologicalSpace X] (x : X) (Z : Set X)
    (hx : x ∈ Z) (hZ : IsClosed Z) :
    Order.krullDim
      {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z} =
      Order.krullDim
        {W : TopologicalSpace.IrreducibleCloseds Z // (⟨x, hx⟩ : Z) ∈ W} := by
  let f : {V : TopologicalSpace.IrreducibleCloseds X // x ∈ V ∧ (V : Set X) ⊆ Z} ↪o
      {W : TopologicalSpace.IrreducibleCloseds Z // (⟨x, hx⟩ : Z) ∈ W} :=
    OrderEmbedding.ofMapLEIff
      (fun V ↦ ⟨irreducibleClosedSubtypeEmbedding Z ⟨V.1, V.2.2⟩, V.2.1⟩)
      (fun _ _ ↦ (irreducibleClosedSubtypeEmbedding Z).le_iff_le)
  have hsurj : Function.Surjective f := by
    intro W
    let V : TopologicalSpace.IrreducibleCloseds X :=
      ⟨Subtype.val '' (W.1 : Set Z),
        W.1.isIrreducible.image _ continuous_subtype_val.continuousOn,
        hZ.isClosedMap_subtype_val _ W.1.isClosed⟩
    have hxV : x ∈ V := ⟨⟨x, hx⟩, W.2, rfl⟩
    have hVZ : (V : Set X) ⊆ Z := by
      rintro y ⟨z, _, rfl⟩
      exact z.2
    refine ⟨⟨V, hxV, hVZ⟩, ?_⟩
    apply Subtype.ext
    apply TopologicalSpace.IrreducibleCloseds.ext
    change Subtype.val ⁻¹' (Subtype.val '' (W.1 : Set Z)) = (W.1 : Set Z)
    exact Set.preimage_image_eq _ Subtype.val_injective
  exact Order.krullDim_eq_of_orderIso (OrderIso.ofSurjective f hsurj)

theorem zeroLocus_local_irreducible_dimension_eq_height
    {R : Type*} [CommRing R] (I : Ideal R) (p : PrimeSpectrum.zeroLocus (I : Set R)) :
    Order.krullDim
      {V : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum.zeroLocus (I : Set R)) // p ∈ V} =
      (Order.height p : WithBot ℕ∞) := by
  let Z := PrimeSpectrum.zeroLocus (I : Set R)
  let e := PrimeSpectrum.zeroLocusEquivIrreducibleCloseds (I : Set R)
  have hmem (q : Z) :
      p ∈ (OrderDual.ofDual (e q) : TopologicalSpace.IrreducibleCloseds Z) ↔ q ≤ p := by
    change p ∈ closure ({q} : Set Z) ↔ q ≤ p
    rw [← specializes_iff_mem_closure]
    exact (subtype_specializes_iff q p).trans (PrimeSpectrum.le_iff_specializes q.1 p.1).symm
  let f : (Set.Iic p)ᵒᵈ ≃o
      {V : TopologicalSpace.IrreducibleCloseds Z // p ∈ V} :=
    { toFun := fun q ↦ ⟨OrderDual.ofDual (e q.1), (hmem q.1).mpr q.2⟩
      invFun := fun V ↦ ⟨e.symm (OrderDual.toDual V.1),
        (hmem (e.symm (OrderDual.toDual V.1))).mp
        (by simpa only [e.apply_symm_apply, OrderDual.ofDual_toDual] using V.2)⟩
      left_inv := fun q ↦ Subtype.ext (e.symm_apply_apply q.1)
      right_inv := fun V ↦ Subtype.ext (e.apply_symm_apply (OrderDual.toDual V.1))
      map_rel_iff' := e.le_iff_le }
  calc
    Order.krullDim {V : TopologicalSpace.IrreducibleCloseds Z // p ∈ V} =
        Order.krullDim (Set.Iic p)ᵒᵈ := (Order.krullDim_eq_of_orderIso f).symm
    _ = Order.krullDim (Set.Iic p) := Order.krullDim_orderDual
    _ = (Order.height p : WithBot ℕ∞) := (Order.height_eq_krullDim_Iic p).symm

theorem ideal_local_irreducible_dimension_eq_localRing
    {R : Type*} [CommRing R] (I : Ideal R) (p : PrimeSpectrum R)
    (hp : I ≤ p.asIdeal) :
    let q := I.primeSpectrumQuotientOrderIsoZeroLocus.symm ⟨p, hp⟩
    Order.krullDim
      {V : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) //
        p ∈ V ∧ (V : Set (PrimeSpectrum R)) ⊆ PrimeSpectrum.zeroLocus (I : Set R)} =
      ringKrullDim (Localization.AtPrime q.asIdeal) := by
  let e := I.primeSpectrumQuotientOrderIsoZeroLocus
  let z : PrimeSpectrum.zeroLocus (I : Set R) := ⟨p, hp⟩
  let q := e.symm z
  rw [local_irreducible_closed_subspace_dimension_eq p _ hp (PrimeSpectrum.isClosed_zeroLocus _),
    zeroLocus_local_irreducible_dimension_eq_height I z]
  have he : Order.height z = Order.height q := by
    simpa only [q, e.apply_symm_apply] using Order.height_orderIso e q
  rw [he, ← PrimeSpectrum.height_eq_orderHeight]
  exact (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal _).symm

end WeightedTorusJets.Geometry

end

section

namespace WeightedTorusJets.Geometry

variable {K : Type*} [Field K]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {K : Type*} [Field K]

theorem laurent_ringKrullDim (n : ℕ) :
    ringKrullDim (AddMonoidAlgebra K (Fin n →₀ ℤ)) = n := by
  rw [ringKrullDim_eq_of_ringEquiv (laurentEquivLocalization K (Fin n)).toRingEquiv]
  exact torus_chart_ringKrullDim n

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {K : Type*} [Field K]

theorem laurent_prime_dimension_codimension (n : ℕ)
    (p : Ideal (AddMonoidAlgebra K (Fin n →₀ ℤ))) [p.IsPrime] :
    ∃ d : ℕ, ringKrullDim (AddMonoidAlgebra K (Fin n →₀ ℤ) ⧸ p) = d ∧
      p.height = (n - d : ℕ) := by
  have := WeightedTorusJets.laurent_finiteType (K := K) (ι := Fin n)
  obtain ⟨d, hdim, _⟩ := WeightedTorusJets.finiteType_dimension_trdeg
    (K := K) (A := AddMonoidAlgebra K (Fin n →₀ ℤ) ⧸ p)
  refine ⟨d, hdim, ?_⟩
  have hsum := prime_height_add_quotient_dim_eq_of_finiteType (K := K) p
  rw [laurent_ringKrullDim, hdim] at hsum
  have he : p.height + (d : ℕ∞) = n := by exact_mod_cast hsum
  have hfin : p.height ≠ ⊤ := by
    intro htop
    simp only [htop, top_add, ENat.top_ne_natCast] at he
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hh] at he ⊢
  have hnat : h + d = n := by exact_mod_cast he
  congr 1
  omega

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {R : Type*} [CommRing R]

end WeightedTorusJets.Geometry

end

section
namespace WeightedTorusJets.Geometry

theorem finiteType_domain_closedPoint_ringKrullDim
    {K A S : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] [CommRing S] [Algebra A S]
    (m : Ideal A) [m.IsMaximal] [IsLocalization.AtPrime S m] :
    ringKrullDim S = ringKrullDim A := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m S]
  exact maximal_height_eq_ringKrullDim_of_finiteType (K := K) m

theorem finiteType_prime_component_closedPoint_dimension
    {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (p m : Ideal A) [p.IsPrime] [m.IsMaximal] (hpm : p ≤ m) :
    let P := m.map (Ideal.Quotient.mk p)
    let : P.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
      Ideal.Quotient.mk_surjective (by simpa using hpm)
    ringKrullDim (Localization.AtPrime P) = ringKrullDim (A ⧸ p) := by
  dsimp only
  let : (m.map (Ideal.Quotient.mk p)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le
      Ideal.Quotient.mk_surjective (by simpa using hpm)
  exact finiteType_domain_closedPoint_ringKrullDim (K := K) (m.map (Ideal.Quotient.mk p))

end WeightedTorusJets.Geometry

end

section

end
end
end

end SiegelZeros

end OAI
