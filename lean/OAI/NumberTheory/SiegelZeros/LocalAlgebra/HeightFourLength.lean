import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import OAI.NumberTheory.SiegelZeros.Determinants.NormalSelection
import OAI.NumberTheory.SiegelZeros.Differentials.CotangentGeneration
import OAI.NumberTheory.SiegelZeros.Differentials.RectangleCotangentBasis
import OAI.NumberTheory.SiegelZeros.Structure.HeightFourIdentity
import OAI.NumberTheory.SiegelZeros.Structure.RectanglePresentation

namespace OAI

noncomputable section

namespace SiegelZeros

namespace WeightedTorusJets.W24

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [IsLocalRing A]

omit [IsLocalRing A] in
theorem augmentation_surjective (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k) : Function.Surjective ε :=
  fun k => ⟨algebraMap K A k, hε k⟩

theorem simple_annihilator_eq_augmentation_kernel (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    Module.annihilator A M = RingHom.ker ε := by
  have hker : (RingHom.ker ε).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective ε (augmentation_surjective ε hε)
  exact (IsLocalRing.eq_maximalIdeal (IsSimpleModule.annihilator_isMaximal (R := A)
    (M := M))).trans (IsLocalRing.eq_maximalIdeal hker).symm

theorem simple_smul_eq_augmentation_smul (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [IsSimpleModule A M] (a : A) (x : M) :
    a • x = ε a • x := by
  have ha : a - algebraMap K A (ε a) ∈ Module.annihilator A M := by
    rw [simple_annihilator_eq_augmentation_kernel ε hε]
    rw [RingHom.mem_ker, map_sub, hε, sub_self]
  have hx := Module.mem_annihilator.mp ha x
  exact sub_eq_zero.mp (by simpa only [sub_smul, algebraMap_smul] using hx)

theorem simple_over_coefficient_field (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [IsSimpleModule A M] : IsSimpleModule K M := by
  apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
  refine ⟨IsSimpleModule.nontrivial A M, ?_⟩
  intro x hx y
  obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective A hx y
  refine ⟨ε a, ?_⟩
  change ε a • x = y
  rw [← simple_smul_eq_augmentation_smul ε hε a x]
  exact ha

theorem length_eq_coefficient_length (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) :
    ∀ [Module K M] [IsScalarTower K A M], Module.length A M = Module.length K M := by
  induction hM with
  | of_subsingleton =>
    intro _ _
    simp only [Module.length_eq_zero]
  | @of_simple_quotient M _ _ N hsimple hN ih =>
    intro _ _
    have : IsSimpleModule K (M ⧸ N) := simple_over_coefficient_field ε hε
    have hexact : Function.Exact N.subtype N.mkQ := by
      rw [LinearMap.exact_iff, Submodule.range_subtype, Submodule.ker_mkQ]
    have hA := Module.length_eq_add_of_exact N.subtype N.mkQ
      (Submodule.subtype_injective N) (Submodule.mkQ_surjective N) hexact
    have hK := Module.length_eq_add_of_exact (N.subtype.restrictScalars K)
      (N.mkQ.restrictScalars K) (Submodule.subtype_injective N)
      (Submodule.mkQ_surjective N) hexact
    calc
      Module.length A M = Module.length A N + Module.length A (M ⧸ N) := hA
      _ = Module.length K N + Module.length K (M ⧸ N) := by
        rw [ih, Module.length_eq_one A (M ⧸ N), Module.length_eq_one K (M ⧸ N)]
      _ = Module.length K M := hK.symm

theorem module_length_eq_finrank_of_augmentation (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [Module.Finite K M] :
    Module.length A M = Module.finrank K M := by
  have : IsNoetherian A M := isNoetherian_of_tower K inferInstance
  have : IsArtinian A M := isArtinian_of_tower K inferInstance
  have hM : IsFiniteLength A M := isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨inferInstance, inferInstance⟩
  rw [length_eq_coefficient_length ε hε hM, Module.length_eq_finrank]

theorem ring_length_eq_finrank_of_augmentation [Module.Finite K A] (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k) :
    Module.length A A = Module.finrank K A :=
  module_length_eq_finrank_of_augmentation ε hε

end WeightedTorusJets.W24

namespace WeightedTorusJets.W25

variable {σ K : Type*} [Fintype σ] [Field K]

omit [Fintype σ] in
@[simp] theorem augmentation_algebraMap (t : σ → ℕ) (c : K) :
    augmentation (K := K) t (algebraMap K (MvPolynomial σ K ⧸ truncationIdeal (K := K) t) c) = c := by
  change (MvPolynomial.C c : MvPolynomial σ K).coeff 0 = c
  simp

theorem intrinsic_length_truncatedQuotient (t : σ → ℕ) :
    Module.length (MvPolynomial σ K ⧸ truncationIdeal (K := K) t)
      (MvPolynomial σ K ⧸ truncationIdeal (K := K) t) = (∏ i, (t i + 1) : ℕ) := by
  calc
    Module.length (MvPolynomial σ K ⧸ truncationIdeal (K := K) t)
        (MvPolynomial σ K ⧸ truncationIdeal (K := K) t) =
        (Module.finrank K (MvPolynomial σ K ⧸ truncationIdeal (K := K) t) : ℕ∞) := by
      exact WeightedTorusJets.W24.module_length_eq_finrank_of_augmentation
        (K := K) (A := MvPolynomial σ K ⧸ truncationIdeal (K := K) t)
        (M := MvPolynomial σ K ⧸ truncationIdeal (K := K) t)
        (augmentation (K := K) t) (augmentation_algebraMap (K := K) t)
    _ = (∏ i, (t i + 1) : ℕ) :=
      congrArg (fun n : ℕ => (n : ℕ∞)) (finrank_truncatedQuotient (K := K) t)

end WeightedTorusJets.W25

namespace WeightedTorusJets.W24

attribute [local instance] Ideal.Quotient.field
attribute [local instance 2000] Monoid.toMulAction Semiring.toModule

open Result.Workers.W57

theorem intrinsic_length_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) : Module.length A A = Module.length B B := by
  have := RingHomInvPair.of_ringEquiv e
  have := this.symm
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e.toSemilinearEquiv)]

theorem length_le_quotient_of_surjective {A B : Type*} [CommRing A] [CommRing B]
    (J : Ideal A) (f : A →+* B) (hJ : J ≤ RingHom.ker f)
    (hf : Function.Surjective f) : Module.length B B ≤ Module.length A (A ⧸ J) := by
  let qf : (A ⧸ J) →+* B := Ideal.Quotient.lift J f (fun _ hx => RingHom.mem_ker.mp (hJ hx))
  have hqf : Function.Surjective qf := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨Ideal.Quotient.mk J x, hx⟩
  let : Algebra (A ⧸ J) B := qf.toAlgebra
  have ha : Function.Surjective (algebraMap (A ⧸ J) B) := hqf
  have hlen : Module.length B B ≤ Module.length (A ⧸ J) (A ⧸ J) := by
    rw [← Module.length_eq_of_surjective (M := B) ha]
    exact Module.length_le_of_surjective (Algebra.linearMap (A ⧸ J) B) ha
  have hquot : Function.Surjective (algebraMap A (A ⧸ J)) := Ideal.Quotient.mk_surjective
  rw [Module.length_eq_of_surjective (M := A ⧸ J) hquot]
  exact hlen

variable (K : Type*) [Field K]

theorem intrinsic_length_rectangleJet (t : Fin 3 → ℕ) :
    Module.length (RectangleJet K (t 0 + 1) (t 1 + 1) (t 2 + 1))
      (RectangleJet K (t 0 + 1) (t 1 + 1) (t 2 + 1)) =
      (∏ i, (t i + 1) : ℕ) := by
  exact (intrinsic_length_ringEquiv (W25.polynomialRectangleEquiv K t)).symm.trans
    (W25.intrinsic_length_truncatedQuotient (K := K) t)

theorem rectangleResidue_polynomialRectangleEquiv (t : Fin 3 → ℕ)
    (x : MvPolynomial (Fin 3) K ⧸ W25.truncationIdeal t) :
    rectangleResidue K (t 0 + 1) (t 1 + 1) (t 2 + 1)
      (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      (W25.polynomialRectangleEquiv K t x) = W25.augmentation t x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change rectangleResidue K (t 0 + 1) (t 1 + 1) (t 2 + 1)
      (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      (W25.polynomialRectangleMap K t p) = p.coeff 0
  change rectangleResidue K _ _ _ _ _ _
    (rectangleProjection K _ _ _ (W25.polynomialSeries K p)) = p.coeff 0
  rw [rectangleResidue_projection]
  simpa only [Finsupp.zero_apply] using W25.coeff_polynomialSeries K p 0

theorem rectangleAugmentation_eq_map (t : Fin 3 → ℕ) :
    rectangleAugmentation K (t 0 + 1) (t 1 + 1) (t 2 + 1)
      (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) =
      (W25.augmentationIdeal t).map (W25.polynomialRectangleEquiv K t).toRingHom := by
  have hc : (rectangleAugmentation K (t 0 + 1) (t 1 + 1) (t 2 + 1)
      (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)).comap
      (W25.polynomialRectangleEquiv K t).toRingHom = W25.augmentationIdeal t := by
    ext x
    change rectangleResidue K _ _ _ _ _ _ (W25.polynomialRectangleEquiv K t x) = 0 ↔
      W25.augmentation t x = 0
    rw [rectangleResidue_polynomialRectangleEquiv]
  rw [← hc, Ideal.map_comap_of_surjective
    (W25.polynomialRectangleEquiv K t).toRingHom (W25.polynomialRectangleEquiv K t).surjective]

theorem rectangleAugmentation_pow_eq_bot (t : Fin 3 → ℕ) :
    (rectangleAugmentation K (t 0 + 1) (t 1 + 1) (t 2 + 1)
      (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)) ^
        ((∑ i, t i) + 1) = ⊥ := by
  rw [rectangleAugmentation_eq_map, ← Ideal.map_pow,
    W25.augmentationIdeal_pow_eq_bot, Ideal.map_bot]

theorem selectedFirst_polynomialRectangleEquiv (t : Fin 3 → ℕ)
    (j : { j : Fin 3 // 0 < t j })
    (x : MvPolynomial (Fin 3) K ⧸ W25.truncationIdeal t) :
    selectedFirst K (fun j => t j + 1) (fun _ => Nat.zero_lt_succ _) j
      (Nat.succ_lt_succ j.property) (W25.polynomialRectangleEquiv K t x) =
      W25.quotientFirstCoefficient (K := K) t j x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [W25.quotientFirstCoefficient_mk]
  change selectedFirst K (fun j => t j + 1) (fun _ => Nat.zero_lt_succ _) j
    (Nat.succ_lt_succ j.property) (W25.polynomialRectangleMap K t p) = _
  have hc := W25.coeff_polynomialSeries K p (Finsupp.single j.val 1)
  rcases j with ⟨j, hj⟩
  fin_cases j <;>
    simpa [selectedFirst, W25.polynomialRectangleMap, rectangleCoeff_projection,
      Finsupp.single_apply] using hc

theorem rectangle_mem_square_of_coefficients_zero (t : Fin 3 → ℕ)
    (y : RectangleJet K (t 0 + 1) (t 1 + 1) (t 2 + 1))
    (hc : rectangleResidue K _ _ _ (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      (Nat.zero_lt_succ _) y = 0)
    (hf : ∀ j : { j : Fin 3 // 0 < t j },
      selectedFirst K (fun j => t j + 1) (fun _ => Nat.zero_lt_succ _) j
        (Nat.succ_lt_succ j.property) y = 0) :
    y ∈ (rectangleAugmentation K (t 0 + 1) (t 1 + 1) (t 2 + 1)
      (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)) ^ 2 := by
  obtain ⟨x, rfl⟩ := (W25.polynomialRectangleEquiv K t).surjective y
  have hp : x ∈ W25.augmentationIdeal t ^ 2 := by
    apply W25.mem_augmentationSquare_of_coefficients_zero t x
    · rwa [rectangleResidue_polynomialRectangleEquiv] at hc
    · intro j
      simpa only [selectedFirst_polynomialRectangleEquiv] using hf j
  rw [rectangleAugmentation_eq_map, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem (W25.polynomialRectangleEquiv K t).toRingHom hp

variable [Algebra ℚ K]

theorem selectedCotangent_coordinates_injective (t : Fin 3 → ℕ) :
    Function.Injective (fun z :
      (rectangleAugmentation K (t 0 + 1) (t 1 + 1) (t 2 + 1)
        (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)).Cotangent =>
      fun j : { j : Fin 3 // 0 < t j } =>
        selectedCotangentCoefficient K (fun j => t j + 1)
          (fun _ => Nat.zero_lt_succ _) j (Nat.succ_lt_succ j.property) z) := by
  intro x y hxy
  let J := rectangleAugmentation K (t 0 + 1) (t 1 + 1) (t 2 + 1)
    (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
  obtain ⟨x, rfl⟩ := J.toCotangent_surjective x
  obtain ⟨y, rfl⟩ := J.toCotangent_surjective y
  apply J.toCotangent_eq.mpr
  apply rectangle_mem_square_of_coefficients_zero K t
  · change rectangleResidue K _ _ _ _ _ _ ((x : RectangleJet K (t 0 + 1) (t 1 + 1) (t 2 + 1)) -
      (y : RectangleJet K (t 0 + 1) (t 1 + 1) (t 2 + 1))) = 0
    have hx : rectangleResidue K (t 0 + 1) (t 1 + 1) (t 2 + 1)
        (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
        (x : RectangleJet K (t 0 + 1) (t 1 + 1) (t 2 + 1)) = 0 := x.property
    have hy : rectangleResidue K (t 0 + 1) (t 1 + 1) (t 2 + 1)
        (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
        (y : RectangleJet K (t 0 + 1) (t 1 + 1) (t 2 + 1)) = 0 := y.property
    rw [map_sub, hx, hy, sub_self]
  · intro j
    rw [map_sub]
    apply sub_eq_zero.mpr
    exact congrFun hxy j

section CoordinateBridge

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R]

theorem selectedTaylorCotangent_surjective_of_coordinate_injective
    (D : Fin 3 → Derivation ℚ R R) (t : Fin 3 → ℕ)
    (hinj : Function.Injective (fun z :
      (rectangleAugmentation (IsLocalRing.ResidueField R)
        (t 0 + 1) (t 1 + 1) (t 2 + 1)
        (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)).Cotangent =>
      fun j : { j : Fin 3 // 0 < t j } =>
        selectedCotangentCoefficient (IsLocalRing.ResidueField R)
          (fun j => t j + 1) (fun _ => Nat.zero_lt_succ _) j
          (Nat.succ_lt_succ j.property) z))
    (hD : Function.Surjective (fun x : IsLocalRing.maximalIdeal R =>
      fun j : { j : Fin 3 // 0 < t j } => IsLocalRing.residue R (D j x))) :
    Function.Surjective (selectedSourceTaylorCotangent (IsLocalRing.maximalIdeal R) D
      (fun j => t j + 1) (fun _ => Nat.zero_lt_succ _)) := by
  intro z
  obtain ⟨x, hx⟩ := hD (fun j =>
    selectedCotangentCoefficient (IsLocalRing.ResidueField R)
      (fun j => t j + 1) (fun _ => Nat.zero_lt_succ _) j
      (Nat.succ_lt_succ j.property) z)
  refine ⟨(IsLocalRing.maximalIdeal R).toCotangent x, hinj ?_⟩
  funext j
  change selectedCotangentCoefficient (R ⧸ IsLocalRing.maximalIdeal R)
      (fun j => t j + 1) (fun _ => Nat.zero_lt_succ _) j
      (Nat.succ_lt_succ j.property)
      (selectedSourceTaylorCotangent (IsLocalRing.maximalIdeal R) D
        (fun j => t j + 1) (fun _ => Nat.zero_lt_succ _)
        ((IsLocalRing.maximalIdeal R).toCotangent x)) = _
  rw [selectedSourceTaylorCotangent_coefficient, SiegelZeros.W58.derivationNormal_toCotangent]
  exact congrFun hx j

end CoordinateBridge

section ActualLocalTaylor

variable {R : Type*} [CommRing R] [Algebra ℚ R] [IsLocalRing R]

theorem local_rectangularJet_surjective (D : Fin 3 → Derivation ℚ R R)
    (t : Fin 3 → ℕ)
    (hD : Function.Surjective (fun x : IsLocalRing.maximalIdeal R =>
      fun j : { j : Fin 3 // 0 < t j } => IsLocalRing.residue R (D j x))) :
    Function.Surjective (rectangularJetHom (IsLocalRing.ResidueField R)
      (D 0) (D 1) (D 2) (IsLocalRing.residue R) (t 0 + 1) (t 1 + 1) (t 2 + 1)) := by
  let I := IsLocalRing.maximalIdeal R
  let J := rectangleAugmentation (IsLocalRing.ResidueField R)
    (t 0 + 1) (t 1 + 1) (t 2 + 1)
    (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
  let f := rectangularJetAlgHom (IsLocalRing.ResidueField R) D (IsLocalRing.residue R)
    (t 0 + 1) (t 1 + 1) (t 2 + 1)
  have hf : I ≤ J.comap f := by
    exact ideal_le_augmentation_comap (IsLocalRing.ResidueField R) (D 0) (D 1) (D 2)
      (IsLocalRing.residue R) _ _ _ _ _ _ I (by rw [IsLocalRing.ker_residue])
  refine algHom_surjective_of_residue_cotangent I J f hf (IsLocalRing.residue R)
    (rectangleResidue (IsLocalRing.ResidueField R) _ _ _ _ _ _)
    IsLocalRing.residue_surjective ?_ rfl ?_ ((∑ j, t j) + 1) ?_
  · ext x
    exact rectangleResidue_taylor (IsLocalRing.ResidueField R)
      (D 0) (D 1) (D 2) (IsLocalRing.residue R)
      (t 0 + 1) (t 1 + 1) (t 2 + 1)
      (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) x
  · have hs := selectedTaylorCotangent_surjective_of_coordinate_injective (R := R) D t
      (selectedCotangent_coordinates_injective (IsLocalRing.ResidueField R) t) hD
    intro z
    obtain ⟨x, hx⟩ := hs z
    refine ⟨x, ?_⟩
    have he : Ideal.mapCotangent I J f hf x =
        selectedSourceTaylorCotangent I D (fun j => t j + 1)
          (fun _ => Nat.zero_lt_succ _) x := by
      obtain ⟨a, rfl⟩ := I.toCotangent_surjective x
      rw [selectedSourceTaylorCotangent, Ideal.mapCotangent_toCotangent,
        Ideal.mapCotangent_toCotangent]
      apply congrArg J.toCotangent
      apply Subtype.ext
      rfl
    exact he.trans hx
  · exact rectangleAugmentation_pow_eq_bot (IsLocalRing.ResidueField R) t

end ActualLocalTaylor

open SiegelZeros.W23 SiegelZeros.W58 SiegelZerosAwei.W21

@[reducible] local instance componentLocalRatModule
    (P : Ideal (TorusRing K)) [P.IsPrime] :
    Module ℚ (Localization.AtPrime P) := Algebra.toModule

@[reducible] local instance componentLocalBaseModule
    (P : Ideal (TorusRing K)) [P.IsPrime] :
    Module K (Localization.AtPrime P) := Algebra.toModule

@[reducible] local instance componentLocalTorusModule
    (P : Ideal (TorusRing K)) [P.IsPrime] :
    Module (TorusRing K) (Localization.AtPrime P) := Algebra.toModule

local instance componentLocalHasQuotient (P : Ideal (TorusRing K)) [P.IsPrime] :
    HasQuotient (Localization.AtPrime P) (Ideal (Localization.AtPrime P)) :=
  @Ideal.instHasQuotient (Localization.AtPrime P) inferInstance

theorem component_length_lower_of_derivative_evaluation
    (v : Fin 3 → Fin 4 → K) (F : AmbientPolynomial K) (t s : Fin 3 → ℕ)
    (b : ℕ) (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : derivativeIdeal v F t (b + 1) ≤ P) (hst : ∀ j, s j ≤ t j)
    (hD : Function.Surjective (fun x : IsLocalRing.maximalIdeal (Localization.AtPrime P) =>
      fun j : { j : Fin 3 // 0 < s j } => IsLocalRing.residue (Localization.AtPrime P)
        (componentDerivation P (v j) x))) :
    (∏ j, (s j + 1) : ℕ) ≤
      Module.length (Localization.AtPrime P)
        (Localization.AtPrime P ⧸ (derivativeIdeal v F t b).map
          (algebraMap (TorusRing K) (Localization.AtPrime P))) := by

  have hsraw := local_rectangularJet_surjective (R := Localization.AtPrime P)
    (fun j => componentDerivation P (v j)) s hD
  have hs : Function.Surjective (componentJet v s P) := by
    intro y
    obtain ⟨x, hx⟩ := hsraw y
    refine ⟨x, ?_⟩
    change rectangularJetHom (IsLocalRing.ResidueField (Localization.AtPrime P))
      (componentDerivation P (v 0)) (componentDerivation P (v 1))
      (componentDerivation P (v 2)) (IsLocalRing.residue (Localization.AtPrime P))
      (s 0 + 1) (s 1 + 1) (s 2 + 1) x = y
    exact hx
  have hl := length_le_quotient_of_surjective
    ((derivativeIdeal v F t b).map (algebraMap (TorusRing K) (Localization.AtPrime P)))
    (componentJet v s P)
    (localized_derivativeIdeal_le_smaller_componentJet_ker v F t s b P hP hst) hs
  exact (intrinsic_length_rectangleJet
    (IsLocalRing.ResidueField (Localization.AtPrime P)) s).symm.le.trans hl

theorem selected_component_length_lower
    (v : Fin 3 → Fin 4 → K) (F : AmbientPolynomial K) (t : Fin 3 → ℕ)
    (S : Set (Fin 3)) (b : ℕ) (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : derivativeIdeal v F t (b + 1) ≤ P)
    (hD : Function.Surjective (fun x : IsLocalRing.maximalIdeal (Localization.AtPrime P) =>
      fun j : S => IsLocalRing.residue (Localization.AtPrime P)
        (W18.localTorusDerivation K P (v j) x))) :
    (∏ j, (selectedCutoffs t S j + 1) : ℕ) ≤
      Module.length (Localization.AtPrime P)
        (Localization.AtPrime P ⧸ (derivativeIdeal v F t b).map
          (algebraMap (TorusRing K) (Localization.AtPrime P))) := by
  classical
  apply component_length_lower_of_derivative_evaluation K v F t (selectedCutoffs t S)
    b P hP (selectedCutoffs_le t S)
  intro a
  let z : S → IsLocalRing.ResidueField (Localization.AtPrime P) := fun j =>
    if hj : 0 < selectedCutoffs t S j then a ⟨j, hj⟩ else 0
  obtain ⟨x, hx⟩ := hD z
  refine ⟨x, ?_⟩
  funext j
  have hjS : j.val ∈ S := by
    by_contra hn
    have he := selectedCutoffs_of_not_mem t S j hn
    have hp := j.property
    rw [he] at hp
    exact Nat.lt_irrefl 0 hp
  have hval := congrFun hx (⟨j, hjS⟩ : S)
  change IsLocalRing.residue (Localization.AtPrime P)
    (componentDerivation P (v j) (x : Localization.AtPrime P)) = a j
  rw [componentDerivation_eq_localTorus_restrict]
  simpa only [z, dite_eq_left j.property, Derivation.restrictScalars_apply] using hval

open ActualNormalSelection NormalExactness

attribute [local instance] ActualNormalSelection.genericLocalCommSemiring
  ActualNormalSelection.genericResidueSelfModule
  ActualNormalSelection.genericNormalDualModule
  ActualNormalSelection.genericQuotientNormalDualModule
  ActualNormalSelection.genericLogKernelModule

theorem generic_component_length_lower [PerfectField K]
    (P : Ideal (TorusRing K)) [P.IsPrime] (h : ℕ) (hp : P.height = h)
    (c : Fin 4 → GenericResidue K P)
    (hω : residueLogForm (K := K) (GenericMaximal K P) c
      (genericCoordinates K P) ≠ 0)
    (v : Fin 3 → Fin 4 → K)
    (β : Module.Basis (Fin 3) (GenericResidue K P)
      (logFormOnDerivations (K := K) (GenericMaximal K P) c
        (genericCoordinates K P)).ker)
    (hβ : ∀ i, (β i).val = reducedDerivation (GenericMaximal K P)
      (W18.localTorusDerivation K P (v i)))
    (F : AmbientPolynomial K) (t : Fin 3 → ℕ) (b : ℕ)
    (hP : derivativeIdeal v F t (b + 1) ≤ P) :
    ∃ S : Set (Fin 3), Nat.card S = h ∧
      (∏ j, (selectedCutoffs t S j + 1) : ℕ) ≤
        Module.length (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ (derivativeIdeal v F t b).map
            (algebraMap (TorusRing K) (Localization.AtPrime P))) := by
  obtain ⟨S, hcard, _, hs⟩ :=
    generic_original_direction_selection K P h hp c hω v β hβ
  exact ⟨S, hcard, selected_component_length_lower K v F t S b P hP hs⟩

theorem identity_component_length_lower
    (v : Fin 3 → Fin 4 → K) (hv : LinearIndependent K v)
    (F : AmbientPolynomial K) (t : Fin 3 → ℕ) (b : ℕ)
    (hP : derivativeIdeal v F t (b + 1) ≤ identityIdeal K) :
    (∏ j, (t j + 1) : ℕ) ≤
      Module.length (Localization.AtPrime (identityIdeal K))
        (Localization.AtPrime (identityIdeal K) ⧸ (derivativeIdeal v F t b).map
          (algebraMap (TorusRing K) (Localization.AtPrime (identityIdeal K)))) := by
  classical
  have hn := (identity_three_selected_normals K v hv).2
  have hs : Function.Surjective
      (fun x : IsLocalRing.maximalIdeal (Localization.AtPrime (identityIdeal K)) =>
        fun j : (Set.univ : Set (Fin 3)) =>
          IsLocalRing.residue (Localization.AtPrime (identityIdeal K))
            (W18.localTorusDerivation K (identityIdeal K) (v j) x)) := by
    intro a
    obtain ⟨x, hx⟩ := hn (fun j => a ⟨j, Set.mem_univ j⟩)
    exact ⟨x, funext (fun j => congrFun hx j)⟩
  simpa only [selectedCutoffs, Set.mem_univ, ↓reduceIte] using
    selected_component_length_lower K v F t Set.univ b (identityIdeal K) hP hs

end WeightedTorusJets.W24

namespace SiegelZerosAwei.W21

open SiegelZeros.W58
variable {K : Type*} [Field K] [Algebra ℚ K]

local instance (P : Ideal (TorusRing K)) [P.IsPrime] :
    HasQuotient (Localization.AtPrime P) (Ideal (Localization.AtPrime P)) :=
  @Ideal.instHasQuotient (Localization.AtPrime P) inferInstance

theorem height_four_component_length_lower
    (P : Ideal (TorusRing K)) [P.IsPrime]
    (hPid : P ≤ identityIdeal K) (hp : P.height = 4)
    (v : Fin 3 → Fin 4 → K) (hv : LinearIndependent K v)
    (F : AmbientPolynomial K) (t : Fin 3 → ℕ) (b : ℕ)
    (hP : derivativeIdeal v F t (b + 1) ≤ P) :
    (∏ j, (t j + 1) : ℕ) ≤
      Module.length (Localization.AtPrime P)
        (Localization.AtPrime P ⧸ (derivativeIdeal v F t b).map
          (algebraMap (TorusRing K) (Localization.AtPrime P))) := by
  have heq := prime_eq_identityIdeal_of_height_four P hPid hp
  subst P
  exact WeightedTorusJets.W24.identity_component_length_lower K v hv F t b hP

end SiegelZerosAwei.W21

end SiegelZeros

end

end OAI
