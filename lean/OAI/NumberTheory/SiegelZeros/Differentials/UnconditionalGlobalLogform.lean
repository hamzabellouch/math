import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring
import OAI.NumberTheory.SiegelZeros.Determinants.NormalDirectionSelection
import OAI.NumberTheory.SiegelZeros.Determinants.NormalSurjectivity
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.DVRLocalCoordinates
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.GenericResidueFunctionField
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.GlobalStalkExtension
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.ResidueIndependence
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.ResidueMap
import OAI.NumberTheory.SiegelZeros.Selection.CoordinateConstancy
import OAI.NumberTheory.SiegelZeros.Structure.DvrFractions

namespace OAI

noncomputable section

namespace SiegelZeros

namespace SiegelZerosAwei.Workers.W14
open scoped BigOperators

theorem logform_zero_transport {k F G ι : Type*} [CommRing k] [Field F] [Field G]
    [Algebra k F] [Algebra k G] [Fintype ι]
    (e : F ≃ₐ[k] G) (c : ι → k) (f : ι → F)
    (h : ∑ i, c i • logDifferential (k := k) (f i) = 0) :
    ∑ i, c i • logDifferential (k := k) (e (f i)) = 0 := by
  let extensionAlgebra : Algebra F G := e.toRingEquiv.toRingHom.toAlgebra
  let extensionScalarTower : IsScalarTower k F G := IsScalarTower.of_algebraMap_eq
    (fun x => (e.commutes x).symm)
  have hmap (x : F) : KaehlerDifferential.map k k F G
      (logDifferential (k := k) x) = logDifferential (k := k) (e x) := by
    rw [logDifferential, map_smul, KaehlerDifferential.map_D,
      ← algebraMap_smul G (x⁻¹)]
    change (e x⁻¹) • KaehlerDifferential.D k G (e x) = _
    rw [map_inv₀]
    rfl
  have he := congrArg ((KaehlerDifferential.map k k F G).restrictScalars k) h
  simpa only [map_sum, map_smul, LinearMap.restrictScalars_apply, hmap, map_zero] using he

open scoped BigOperators

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra ℂ R] [Algebra R K] [Algebra ℂ K] [IsScalarTower ℂ R K]
    [IsFractionRing R K] [Algebra.FormallySmooth ℂ R]
    [Algebra.FormallySmooth ℂ (IsLocalRing.ResidueField R)]

theorem independent_logform_zero_forces_equal_orders {ι : Type*} [Fintype ι]
    {c : ι → ℂ} (hc : LinearIndependent ℚ c) (f : ι → K)
    (hf : ∀ i, f i ≠ 0) {π : R} (hπ : Irreducible π)
    (hform : ∑ i, c i • logDifferential (k := ℂ) (f i) = 0) :
    ∀ i, ∃ x y : R,
      f i = algebraMap R K x / algebraMap R K y ∧
      IsDiscreteValuationRing.addVal R x = IsDiscreteValuationRing.addVal R y := by
  classical
  choose x y n m hmem hxy hn hm hres using
    (fun i => logarithmicResidue_dlog (k := ℂ) (R := R) (hf i) hπ)
  have hr := logarithmicResidue_sum_eq_zero (k := ℂ) (K := K) hπ
    (fun i => algebraMap ℂ R (c i))
    (fun i => ⟨logDifferential (k := ℂ) (f i), hmem i⟩)
    (by simpa only [algebraMap_smul] using hform)
  have hz : ∀ i, (n i : ℤ) - (m i : ℤ) = 0 := by
    apply residue_field_integer_relation_eq_zero hc
      (algebraMap ℂ (IsLocalRing.ResidueField R))
    simpa only [hres, ← IsScalarTower.algebraMap_apply ℂ R
      (IsLocalRing.ResidueField R)] using hr
  intro i
  refine ⟨x i, y i, hxy i, ?_⟩
  have hnm : n i = m i := Int.natCast_inj.mp (sub_eq_zero.mp (hz i))
  rw [hn i, hm i, hnm]

theorem independent_logform_zero_forces_local_regularity {ι : Type*} [Fintype ι]
    {c : ι → ℂ} (hc : LinearIndependent ℚ c) (f : ι → K)
    (hf : ∀ i, f i ≠ 0)
    (hform : ∑ i, c i • logDifferential (k := ℂ) (f i) = 0) :
    ∀ i, f i ∈ (algebraMap R K).range ∧ (f i)⁻¹ ∈ (algebraMap R K).range := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  intro i
  obtain ⟨x, y, hxy, hv⟩ :=
    independent_logform_zero_forces_equal_orders hc f hf hπ hform i
  have hx : x ≠ 0 := by
    intro hx
    apply hf i
    rw [hxy, hx, map_zero, zero_div]
  have hy : y ≠ 0 := by
    intro hy
    apply hf i
    rw [hxy, hy, map_zero, div_zero]
  rw [hxy]
  exact fraction_and_inverse_mem_range_of_addVal_eq hx hy hv

end SiegelZerosAwei.Workers.W14

namespace WeightedTorusJets.NormalExactness

section

variable {K R J : Type*} [CommRing K] [CommRing R] [Algebra K R]
variable [Fintype J] (I : Ideal R) [I.IsMaximal]

attribute [local instance] Ideal.Quotient.field

def residueLogForm (c : J → R ⧸ I) (u : J → R) :
    KaehlerDifferential K (R ⧸ I) :=
  ∑ j, c j • SiegelZerosAwei.Workers.W14.logDifferential (k := K)
    (Ideal.Quotient.mk I (u j))

def logFormOnDerivations (c : J → R ⧸ I) (u : J → R) :
    Derivation K R (R ⧸ I) →ₗ[R ⧸ I] R ⧸ I where
  toFun D := ∑ j, (c j * (Ideal.Quotient.mk I (u j))⁻¹) * D (u j)
  map_add' D E := by
    simp only [Derivation.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a D := by
    simp only [Derivation.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem tangent_logForm_pairing (c : J → R ⧸ I) (u : J → R)
    (f : KaehlerDifferential K (R ⧸ I) →ₗ[R ⧸ I] R ⧸ I) :
    logFormOnDerivations I c u
      (tangentInclusion I (f.compDer (KaehlerDifferential.D K (R ⧸ I)))) =
        f (residueLogForm (K := K) I c u) := by
  simp only [logFormOnDerivations,
    residueLogForm, map_sum, map_smul,
    SiegelZerosAwei.Workers.W14.logDifferential, smul_eq_mul, mul_assoc]
  rfl

theorem exists_tangent_not_annihilated (c : J → R ⧸ I) (u : J → R)
    (hω : residueLogForm (K := K) I c u ≠ 0) :
    ∃ E : Derivation K (R ⧸ I) (R ⧸ I),
      logFormOnDerivations I c u (tangentInclusion I E) ≠ 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (R ⧸ I) hω
  refine ⟨f.compDer (KaehlerDifferential.D K (R ⧸ I)), ?_⟩
  rwa [tangent_logForm_pairing]

end

variable {K R J : Type*} [CommRing K] [CommRing R] [Algebra K R]
variable [Fintype J] (I : Ideal R) [I.IsMaximal]
attribute [local instance] Ideal.Quotient.field
variable (c : J → R ⧸ I) (u : J → R)

def logarithmicNormalMap :
    (logFormOnDerivations (K := K) I c u).ker →ₗ[R ⧸ I]
      (I.Cotangent →ₗ[R ⧸ I] R ⧸ I) :=
  (normalRestriction I).comp (logFormOnDerivations I c u).ker.subtype

theorem logarithmicNormalMap_surjective
    [Algebra.FormallySmooth K R] [Algebra.FormallySmooth K (R ⧸ I)]
    (hω : residueLogForm (K := K) I c u ≠ 0) :
    Function.Surjective (logarithmicNormalMap (K := K) I c u) := by
  intro φ
  obtain ⟨D, hD⟩ := normalRestriction_surjective (K := K) I φ
  obtain ⟨E, hE⟩ := exists_tangent_not_annihilated I c u hω
  have hN : normalRestriction I (tangentInclusion I E) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [normalRestriction_kernel_eq_tangent_range]
    exact LinearMap.mem_range.mpr ⟨E, rfl⟩
  obtain ⟨w, hw, hsplit⟩ :=
    HyperplaneNormal.exists_kernel_decomposition (logFormOnDerivations I c u) hE D
  refine ⟨⟨w, hw⟩, ?_⟩
  change normalRestriction I w = φ
  rw [hsplit, map_add, map_smul, hN, smul_zero, add_zero] at hD
  exact hD

theorem select_actual_logarithmic_normals
    [Algebra.FormallySmooth K R] [Algebra.FormallySmooth K (R ⧸ I)]
    (hω : residueLogForm (K := K) I c u ≠ 0)
    (b : Module.Basis (Fin 3) (R ⧸ I) (logFormOnDerivations (K := K) I c u).ker) :
    ∃ S : Set (Fin 3),
      LinearIndependent (R ⧸ I)
        (fun i : S => logarithmicNormalMap (K := K) I c u (b i)) ∧
      Submodule.span (R ⧸ I)
        ((fun i => logarithmicNormalMap (K := K) I c u (b i)) '' S) = ⊤ ∧
      Nat.card S = Module.finrank (R ⧸ I) (I.Cotangent →ₗ[R ⧸ I] R ⧸ I) := by
  have hs : Submodule.span (R ⧸ I)
      (Set.range (fun i => logarithmicNormalMap (K := K) I c u (b i))) = ⊤ := by
    rw [show (fun i => logarithmicNormalMap (K := K) I c u (b i)) =
        logarithmicNormalMap (K := K) I c u ∘ b from rfl,
      Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      LinearMap.range_eq_top.mpr (logarithmicNormalMap_surjective I c u hω)]
  obtain ⟨S, hli, hspan, hcard⟩ := HyperplaneNormal.select_three_directions
    (K := R ⧸ I) (fun i => logarithmicNormalMap (K := K) I c u (b i))
  refine ⟨S, hli, hspan.trans hs, ?_⟩
  rw [hs, finrank_top] at hcard
  exact hcard

end WeightedTorusJets.NormalExactness

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace SiegelZerosAwei.Workers.W14

section
open SiegelZerosAwei.Workers.W15 SiegelZeros.W58

variable (p : Ideal (TorusRing ℂ)) [p.IsPrime]

local instance compactified_top_nonempty :
    Nonempty (⊤ : (NormalizedProjectiveTorus p).Opens) :=
  ⟨⟨genericPoint (NormalizedProjectiveTorus p), trivial⟩⟩

def DivisorFormalSmoothness : Prop :=
  ∀ (x : NormalizedProjectiveTorus p),
    ringKrullDim ((NormalizedProjectiveTorus p).presheaf.stalk x) = 1 →
    letI := schemeStalkAlgebra (normalizedProjectiveTorusToBase p) x
    Algebra.FormallySmooth ℂ ((NormalizedProjectiveTorus p).presheaf.stalk x)

theorem compactified_zero_logform_coordinates_constant
    (hsmooth : DivisorFormalSmoothness p) {c : Fin 4 → ℂ}
    (hc : LinearIndependent ℚ c) :
    letI := compactifiedFunctionFieldAlgebra p
    (∑ i, c i • logDifferential (k := ℂ) (compactifiedTorusCoordinate p i) = 0) →
      ∀ i, ∃ a : ℂ, compactifiedTorusCoordinate p i =
        algebraMap ℂ (NormalizedProjectiveTorus p).functionField a := by
  let compactifiedAlgebra := compactifiedFunctionFieldAlgebra p
  intro hzero i
  have hext : ∃ t : Γ(NormalizedProjectiveTorus p, ⊤),
      (NormalizedProjectiveTorus p).germToFunctionField ⊤ t =
        compactifiedTorusCoordinate p i := by
    apply global_preimage_of_dimensionOne_stalks
      (normalizedProjectiveTorus_stalk_integrallyClosed p)
      (compactifiedTorusCoordinate p i)
    intro x hx
    let stalkAlgebra := schemeStalkAlgebra (normalizedProjectiveTorusToBase p) x
    let stalkDvr := projective_divisor_stalk_dvr p x hx
    let stalkFormallySmooth : Algebra.FormallySmooth ℂ
        ((NormalizedProjectiveTorus p).presheaf.stalk x) := hsmooth x hx
    let residueFormallySmooth := projective_divisor_residue_formallySmooth p x
    let stalkFunctionFieldTower :=
      schemeScalarTower_stalk_functionField (normalizedProjectiveTorusToBase p) x
    exact (independent_logform_zero_forces_local_regularity
      (R := (NormalizedProjectiveTorus p).presheaf.stalk x)
      hc (compactifiedTorusCoordinate p) (compactifiedTorusCoordinate_ne_zero p) hzero i).1
  obtain ⟨a, ha⟩ := rationalFunction_constant_of_global
    (normalizedProjectiveTorusToBase p) (compactifiedTorusCoordinate p i) hext
  refine ⟨a, ?_⟩
  rw [scalarToFunctionField_constantSection] at ha
  exact ha.symm

theorem torus_functionField_logform_ne_zero
    (hsmooth : DivisorFormalSmoothness p) (hp : p ≤ identityIdeal ℂ)
    (hh : p.height ≤ 3) {c : Fin 4 → ℂ} (hc : LinearIndependent ℚ c) :
    letI := torusFunctionFieldAlgebra p
    ∑ i, c i • logDifferential (k := ℂ) (torusCoordinateFunction ℂ p i) ≠ 0 := by
  let compactifiedAlgebra := compactifiedFunctionFieldAlgebra p
  let torusAlgebra := torusFunctionFieldAlgebra p
  intro hzero
  let e := normalizedProjectiveTorusFunctionFieldAlgEquiv p
  have hcompact := logform_zero_transport e.symm c (torusCoordinateFunction ℂ p) hzero
  have hcompact' : ∑ i, c i • logDifferential (k := ℂ)
      (compactifiedTorusCoordinate p i) = 0 := by
    exact hcompact
  have hconstant := compactified_zero_logform_coordinates_constant p hsmooth hc hcompact'
  apply not_all_coordinates_constant p hp hh
  intro i
  obtain ⟨a, ha⟩ := hconstant i
  refine ⟨a, ?_⟩
  have he := congrArg e ha
  simpa only [e, normalizedProjectiveTorusFunctionFieldAlgEquiv_coordinate,
    AlgEquiv.commutes] using he

theorem residueLogForm_zero_scalar_coefficients
    {k R J : Type*} [CommRing k] [CommRing R] [IsLocalRing R]
    [Algebra k R] [Fintype J] (c : J → k) (u : J → R)
    (h : WeightedTorusJets.NormalExactness.residueLogForm (K := k)
      (IsLocalRing.maximalIdeal R)
      (fun i => Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
        (algebraMap k R (c i))) u = 0) :
    ∑ i, c i • logDifferential (k := k)
      (algebraMap R (IsLocalRing.ResidueField R) (u i)) = 0 := by
  change ∑ i, (algebraMap k (IsLocalRing.ResidueField R) (c i)) •
    logDifferential (k := k)
      (algebraMap R (IsLocalRing.ResidueField R) (u i)) = 0 at h
  simpa only [algebraMap_smul] using h

@[reducible] local instance genericLocalCommSemiring :
    CommSemiring (GenericLocalRing ℂ p) :=
  (inferInstance : CommRing (GenericLocalRing ℂ p)).toCommSemiring

theorem torus_residueLogForm_ne_zero
    (hsmooth : DivisorFormalSmoothness p) (hp : p ≤ identityIdeal ℂ)
    (hh : p.height ≤ 3) {c : Fin 4 → ℂ} (hc : LinearIndependent ℚ c) :
    WeightedTorusJets.NormalExactness.residueLogForm (K := ℂ)
      (R := GenericLocalRing ℂ p) (J := Fin 4)
      (IsLocalRing.maximalIdeal (GenericLocalRing ℂ p))
      (fun i => Ideal.Quotient.mk (IsLocalRing.maximalIdeal (GenericLocalRing ℂ p))
        (algebraMap ℂ (GenericLocalRing ℂ p) (c i)))
      (fun i => algebraMap (TorusRing ℂ) (GenericLocalRing ℂ p) (coordinate ℂ i)) ≠ 0 := by
  let torusAlgebra := torusFunctionFieldAlgebra p
  intro hzero
  let κ := IsLocalRing.ResidueField (GenericLocalRing ℂ p)
  have hresidue (x : TorusRing ℂ) :
      algebraMap (GenericLocalRing ℂ p) κ
        (algebraMap (TorusRing ℂ) (GenericLocalRing ℂ p) x) =
        algebraMap (TorusRing ℂ) κ x := rfl
  let e := WeightedTorusJets.GenericResidueFunctionField.genericResidueFunctionFieldAlgEquiv p
  have hcoordinate (i : Fin 4) :
      e (algebraMap (TorusRing ℂ) κ (coordinate ℂ i)) =
        torusCoordinateFunction ℂ p i :=
    WeightedTorusJets.GenericResidueFunctionField.genericResidueFunctionFieldAlgEquiv_coordinate p i
  have hlocal : ∑ i, c i • logDifferential (k := ℂ)
      (algebraMap (TorusRing ℂ) κ (coordinate ℂ i)) = 0 := by
    have hscalar := residueLogForm_zero_scalar_coefficients
      (k := ℂ) (R := GenericLocalRing ℂ p) c
      (fun i => algebraMap (TorusRing ℂ) (GenericLocalRing ℂ p) (coordinate ℂ i)) hzero
    change ∑ i, c i • logDifferential (k := ℂ)
      (algebraMap (GenericLocalRing ℂ p) κ
        (algebraMap (TorusRing ℂ) (GenericLocalRing ℂ p) (coordinate ℂ i))) = 0 at hscalar
    simpa only [hresidue] using hscalar
  have hf := logform_zero_transport e c
    (fun i => algebraMap (TorusRing ℂ) κ (coordinate ℂ i)) hlocal
  apply torus_functionField_logform_ne_zero p hsmooth hp hh hc
  simpa only [hcoordinate] using hf

end

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

open SiegelZerosAwei.Workers.W15 SiegelZeros.W58

variable (p : Ideal (TorusRing ℂ)) [p.IsPrime]

theorem actual_projective_divisor_formallySmooth
    (x : NormalizedProjectiveTorus p)
    (hx : ringKrullDim ((NormalizedProjectiveTorus p).presheaf.stalk x) = 1) :
    letI := schemeStalkAlgebra (normalizedProjectiveTorusToBase p) x
    Algebra.FormallySmooth ℂ ((NormalizedProjectiveTorus p).presheaf.stalk x) := by
  let stalkAlgebra := schemeStalkAlgebra (normalizedProjectiveTorusToBase p) x
  let stalkDvr := projective_divisor_stalk_dvr p x hx
  let stalkEssFiniteType := projective_divisor_stalk_essFiniteType p x
  exact dvr_formallySmooth_of_essFiniteType
    (k := ℂ) (R := (NormalizedProjectiveTorus p).presheaf.stalk x)

theorem actual_divisorFormalSmoothness : DivisorFormalSmoothness p := by
  intro x hx
  exact actual_projective_divisor_formallySmooth p x hx

theorem compactified_zero_logform_coordinates_constant_unconditional
    {c : Fin 4 → ℂ} (hc : LinearIndependent ℚ c) :
    letI := compactifiedFunctionFieldAlgebra p
    (∑ i, c i • logDifferential (k := ℂ) (compactifiedTorusCoordinate p i) = 0) →
      ∀ i, ∃ a : ℂ, compactifiedTorusCoordinate p i =
        algebraMap ℂ (NormalizedProjectiveTorus p).functionField a :=
  compactified_zero_logform_coordinates_constant p (actual_divisorFormalSmoothness p) hc

theorem torus_functionField_logform_ne_zero_unconditional
    (hp : p ≤ identityIdeal ℂ) (hh : p.height ≤ 3)
    {c : Fin 4 → ℂ} (hc : LinearIndependent ℚ c) :
    letI := torusFunctionFieldAlgebra p
    ∑ i, c i • logDifferential (k := ℂ) (torusCoordinateFunction ℂ p i) ≠ 0 :=
  torus_functionField_logform_ne_zero p (actual_divisorFormalSmoothness p) hp hh hc

attribute [local instance] genericLocalCommSemiring

theorem torus_residueLogForm_ne_zero_unconditional
    (hp : p ≤ identityIdeal ℂ) (hh : p.height ≤ 3)
    {c : Fin 4 → ℂ} (hc : LinearIndependent ℚ c) :
    WeightedTorusJets.NormalExactness.residueLogForm (K := ℂ)
      (R := GenericLocalRing ℂ p) (J := Fin 4)
      (IsLocalRing.maximalIdeal (GenericLocalRing ℂ p))
      (fun i => Ideal.Quotient.mk (IsLocalRing.maximalIdeal (GenericLocalRing ℂ p))
        (algebraMap ℂ (GenericLocalRing ℂ p) (c i)))
      (fun i => algebraMap (TorusRing ℂ) (GenericLocalRing ℂ p) (coordinate ℂ i)) ≠ 0 :=
  torus_residueLogForm_ne_zero p (actual_divisorFormalSmoothness p) hp hh hc

end SiegelZerosAwei.Workers.W14

end SiegelZeros

end

end OAI
