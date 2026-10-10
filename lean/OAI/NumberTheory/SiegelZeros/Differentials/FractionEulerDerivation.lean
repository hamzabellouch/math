import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Differentials.LocalizeInvariantDerivationLogCoordinate
import OAI.NumberTheory.SiegelZeros.Structure.InvariantJetLinearMap

namespace OAI

namespace SiegelZeros

section
namespace WeightedTorusJets

theorem biquadratic_torus_log_pairing {K : Type*} [Field K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    let P := MvPolynomial (Fin 4) K
    let z : P := ∏ j : Fin 4, MvPolynomial.X j
    let A := Localization.Away z
    ∃ u : Fin 4 → Aˣ,
      (∀ j, (u j : A) = algebraMap P A (MvPolynomial.X j)) ∧
      ∀ i : Fin 3, ∑ j : Fin 4, algebraMap K A (biquadraticCoefficients a b j) *
        ((↑((u j)⁻¹) : A) *
          Geometry.localizeDerivation (Submonoid.powers z)
            (Geometry.invariantDerivation (biquadraticDirections a b i))
            (algebraMap P A (MvPolynomial.X j))) = 0 := by
  let P := MvPolynomial (Fin 4) K
  let z : P := ∏ j : Fin 4, MvPolynomial.X j
  let A := Localization.Away z
  let u : Fin 4 → Aˣ := fun j => (Geometry.torus_coordinate_isUnit (K := K) j).unit
  have hu (j : Fin 4) : (u j : A) = algebraMap P A (MvPolynomial.X j) :=
    (Geometry.torus_coordinate_isUnit (K := K) j).unit_spec
  refine ⟨u, hu, ?_⟩
  intro i
  have hlog (j : Fin 4) := Geometry.localize_invariantDerivation_log_coordinate
    (Submonoid.powers z) (biquadraticDirections a b i) j (u j) (hu j)
  calc
    _ = ∑ j : Fin 4, algebraMap K A
        (biquadraticCoefficients a b j * biquadraticDirections a b i j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hlog, map_mul]
    _ = algebraMap K A (biquadraticForm a b (biquadraticDirections a b i)) := by
      change _ = algebraMap K A
        (∑ j : Fin 4, biquadraticCoefficients a b j * biquadraticDirections a b i j)
      rw [map_sum]
    _ = 0 := by rw [biquadraticForm_direction ha hb, map_zero]

end WeightedTorusJets

namespace WeightedTorusJets.Geometry

 theorem lift_logarithmicForm_localize_invariantDerivation
    {K F ι : Type*} [Field K] [Field F] [Fintype ι]
    [Algebra K F] [Algebra (MvPolynomial ι K) F] [IsScalarTower K (MvPolynomial ι K) F]
    (M : Submonoid (MvPolynomial ι K)) [IsLocalization M F]
    (c d : ι → K)
    (hx : ∀ i, algebraMap (MvPolynomial ι K) F (MvPolynomial.X i) ≠ 0) :
    (localizeDerivation M (invariantDerivation d)).liftKaehlerDifferential
      (logarithmicForm c (fun i => algebraMap (MvPolynomial ι K) F (MvPolynomial.X i))) =
    algebraMap K F (∑ i, c i * d i) := by
  rw [lift_logarithmicForm, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [localize_invariantDerivation_X, map_mul]
  simp [mul_left_comm, mul_comm, hx i]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

 theorem biquadratic_functionField_logarithmicForm_contraction
    {K : Type*} [Field K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (i : Fin 3) :
    let P := MvPolynomial (Fin 4) K
    let F := FractionRing P
    (Geometry.localizeDerivation (T := F) (nonZeroDivisors P)
      (Geometry.invariantDerivation (biquadraticDirections a b i))).liftKaehlerDifferential
        (Geometry.logarithmicForm (biquadraticCoefficients a b)
          (fun j => algebraMap P F (MvPolynomial.X j))) = 0 := by
  let P := MvPolynomial (Fin 4) K
  let F := FractionRing P
  have hx j : algebraMap P F (MvPolynomial.X j) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective P F)).mpr (MvPolynomial.X_ne_zero j)
  dsimp only
  rw [Geometry.lift_logarithmicForm_localize_invariantDerivation _ _ _ hx]
  change algebraMap K F (biquadraticForm a b (biquadraticDirections a b i)) = 0
  rw [biquadraticForm_direction ha hb, map_zero]

end WeightedTorusJets

namespace WeightedTorusJets

 theorem biquadratic_functionField_contraction_zero_iff
    {K : Type*} [Field K] (a b : K) (v : Fin 4 → K) :
    let P := MvPolynomial (Fin 4) K
    let F := FractionRing P
    (Geometry.localizeDerivation (T := F) (nonZeroDivisors P)
      (Geometry.invariantDerivation v)).liftKaehlerDifferential
        (Geometry.logarithmicForm (biquadraticCoefficients a b)
          (fun j => algebraMap P F (MvPolynomial.X j))) = 0 ↔
      biquadraticForm a b v = 0 := by
  let P := MvPolynomial (Fin 4) K
  let F := FractionRing P
  have hx j : algebraMap P F (MvPolynomial.X j) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective P F)).mpr (MvPolynomial.X_ne_zero j)
  dsimp only
  rw [Geometry.lift_logarithmicForm_localize_invariantDerivation _ _ _ hx]
  change algebraMap K F (biquadraticForm a b v) = 0 ↔ biquadraticForm a b v = 0
  exact map_eq_zero _

 theorem biquadratic_mem_span_iff_functionField_contraction_zero
    {K : Type*} [Field K] [CharZero K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (v : Fin 4 → K) :
    let P := MvPolynomial (Fin 4) K
    let F := FractionRing P
    v ∈ Submodule.span K (Set.range (biquadraticDirections a b)) ↔
    (Geometry.localizeDerivation (T := F) (nonZeroDivisors P)
      (Geometry.invariantDerivation v)).liftKaehlerDifferential
        (Geometry.logarithmicForm (biquadraticCoefficients a b)
          (fun j => algebraMap P F (MvPolynomial.X j))) = 0 := by
  dsimp only
  rw [span_biquadraticDirections_eq_ker ha hb, LinearMap.mem_ker]
  exact (biquadratic_functionField_contraction_zero_iff a b v).symm

end WeightedTorusJets

namespace WeightedTorusJets.Geometry

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

noncomputable def fractionEulerDerivation (i : ι) :
    Derivation K (FractionRing (MvPolynomial ι K)) (FractionRing (MvPolynomial ι K)) :=
  localizeDerivation (nonZeroDivisors (MvPolynomial ι K))
    (invariantDerivation (Pi.single i 1))

 theorem logarithmicTangentMap_fractionEulerDerivation (i : ι) :
    logarithmicTangentMap (k := K)
      (fun j => algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))
        (MvPolynomial.X j)) (fractionEulerDerivation i) = Pi.single i 1 := by
  ext j
  have hx : algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))
      (MvPolynomial.X j) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (MvPolynomial.X_ne_zero j)
  change (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))
      (MvPolynomial.X j))⁻¹ * localizeDerivation _
        (invariantDerivation (Pi.single i (1 : K))) _ = _
  rw [localize_invariantDerivation_X]
  simp [Pi.single_apply, hx]

noncomputable def fractionInvariantDerivationLinearMap :
    (ι → FractionRing (MvPolynomial ι K)) →ₗ[FractionRing (MvPolynomial ι K)]
      Derivation K (FractionRing (MvPolynomial ι K)) (FractionRing (MvPolynomial ι K)) where
  toFun v := ∑ i, v i • fractionEulerDerivation i
  map_add' v w := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

 theorem logarithmicTangentMap_fractionInvariantDerivation (v : ι → FractionRing (MvPolynomial ι K)) :
    logarithmicTangentMap (k := K)
      (fun j => algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))
        (MvPolynomial.X j)) (fractionInvariantDerivationLinearMap v) = v := by
  change logarithmicTangentMap _ (∑ i, v i • fractionEulerDerivation i) = v
  rw [map_sum]
  simp_rw [map_smul, logarithmicTangentMap_fractionEulerDerivation]
  exact (pi_eq_sum_univ' v).symm

omit [Fintype ι] [DecidableEq ι] in
 theorem logarithmicTangentMap_injective_polynomial_fraction :
    Function.Injective (logarithmicTangentMap (k := K)
      (fun j => algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))
        (MvPolynomial.X j))) := by
  intro D E h
  let P := MvPolynomial ι K
  let F := FractionRing P
  apply localization_derivation_ext (nonZeroDivisors P)
  intro p
  change D.compAlgebraMap P p = E.compAlgebraMap P p
  apply MvPolynomial.derivation_eq_of_forall_mem_vars
  intro j _
  have hx : algebraMap P F (MvPolynomial.X j) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (MvPolynomial.X_ne_zero j)
  have hj := congrFun h j
  change (algebraMap P F (MvPolynomial.X j))⁻¹ * D _ =
    (algebraMap P F (MvPolynomial.X j))⁻¹ * E _ at hj
  exact mul_left_cancel₀ (inv_ne_zero hx) hj

noncomputable def fractionLogarithmicTangentEquiv :
    Derivation K (FractionRing (MvPolynomial ι K)) (FractionRing (MvPolynomial ι K))
      ≃ₗ[FractionRing (MvPolynomial ι K)] (ι → FractionRing (MvPolynomial ι K)) :=
  LinearEquiv.ofBijective (logarithmicTangentMap (k := K)
    (fun j => algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))
      (MvPolynomial.X j)))
    ⟨logarithmicTangentMap_injective_polynomial_fraction,
      fun v => ⟨fractionInvariantDerivationLinearMap v,
        logarithmicTangentMap_fractionInvariantDerivation v⟩⟩

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

 theorem fractionLogarithmicTangentEquiv_localize_invariantDerivation (v : ι → K) :
    fractionLogarithmicTangentEquiv (K := K) (ι := ι)
      (localizeDerivation (nonZeroDivisors (MvPolynomial ι K)) (invariantDerivation v)) =
    fun i => algebraMap K (FractionRing (MvPolynomial ι K)) (v i) := by
  ext i
  have hx : algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))
      (MvPolynomial.X i) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (MvPolynomial.X_ne_zero i)
  change (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))
      (MvPolynomial.X i))⁻¹ * localizeDerivation _ (invariantDerivation v) _ = _
  rw [localize_invariantDerivation_X]
  simp [mul_left_comm, hx]

noncomputable def fractionLogarithmicContractionLinearMap (c : ι → K) :
    Derivation K (FractionRing (MvPolynomial ι K)) (FractionRing (MvPolynomial ι K))
      →ₗ[FractionRing (MvPolynomial ι K)] FractionRing (MvPolynomial ι K) where
  toFun D := D.liftKaehlerDifferential (logarithmicForm c
    (fun j => algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K))
      (MvPolynomial.X j)))
  map_add' D E := by
    simp only [lift_logarithmicForm, Derivation.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' t D := by
    simp only [lift_logarithmicForm, Derivation.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

 theorem fractionLogarithmicContraction_eq_dotProduct_comp (c : ι → K) :
    fractionLogarithmicContractionLinearMap c =
    (dotProductBilin (FractionRing (MvPolynomial ι K)) (FractionRing (MvPolynomial ι K))
      (fun i => algebraMap K (FractionRing (MvPolynomial ι K)) (c i))).comp
        fractionLogarithmicTangentEquiv.toLinearMap := by
  ext D
  simp [fractionLogarithmicContractionLinearMap, lift_logarithmicForm,
    dotProductBilin, dotProduct, fractionLogarithmicTangentEquiv, logarithmicTangentMap,
    mul_assoc]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

 theorem biquadratic_functionField_derivations_span_eq_ker
    {K : Type*} [Field K] [CharZero K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    let P := MvPolynomial (Fin 4) K
    let F := FractionRing P
    Submodule.span F (Set.range (fun i : Fin 3 =>
      Geometry.localizeDerivation (T := F) (nonZeroDivisors P)
        (Geometry.invariantDerivation (biquadraticDirections a b i)))) =
    LinearMap.ker (Geometry.fractionLogarithmicContractionLinearMap (biquadraticCoefficients a b)) := by
  let P := MvPolynomial (Fin 4) K
  let F := FractionRing P
  let e := Geometry.fractionLogarithmicTangentEquiv (K := K) (ι := Fin 4)
  have hma : algebraMap K F a ≠ 0 := (map_ne_zero _).mpr ha
  have hmb : algebraMap K F b ≠ 0 := (map_ne_zero _).mpr hb
  have hdirs : (fun i : Fin 3 => e (Geometry.localizeDerivation (T := F) (nonZeroDivisors P)
      (Geometry.invariantDerivation (biquadraticDirections a b i)))) =
      biquadraticDirections (algebraMap K F a) (algebraMap K F b) := by
    exact funext fun i =>
      (Geometry.fractionLogarithmicTangentEquiv_localize_invariantDerivation
        (biquadraticDirections a b i)).trans (map_biquadraticDirections (algebraMap K F) a b i)
  have hcmap : (fun i => algebraMap K F (biquadraticCoefficients a b i)) =
      biquadraticCoefficients (algebraMap K F a) (algebraMap K F b) :=
    map_biquadraticCoefficients (algebraMap K F) a b
  dsimp only
  apply Submodule.map_injective_of_injective e.injective
  rw [Submodule.map_span, ← Set.range_comp', LinearEquiv.coe_coe, hdirs,
    span_biquadraticDirections_eq_ker hma hmb,
    Geometry.fractionLogarithmicContraction_eq_dotProduct_comp,
    hcmap, LinearMap.ker_comp]
  exact (Submodule.map_comap_eq_of_surjective e.surjective _).symm

end WeightedTorusJets

namespace WeightedTorusJets

 theorem biquadratic_functionField_derivations_linearIndependent
    {K : Type*} [Field K] [CharZero K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    let P := MvPolynomial (Fin 4) K
    let F := FractionRing P
    LinearIndependent F (fun i : Fin 3 =>
      Geometry.localizeDerivation (T := F) (nonZeroDivisors P)
        (Geometry.invariantDerivation (biquadraticDirections a b i))) := by
  let P := MvPolynomial (Fin 4) K
  let F := FractionRing P
  let e := Geometry.fractionLogarithmicTangentEquiv (K := K) (ι := Fin 4)
  have hma : algebraMap K F a ≠ 0 := (map_ne_zero _).mpr ha
  have hmb : algebraMap K F b ≠ 0 := (map_ne_zero _).mpr hb
  have hdirs : (fun i : Fin 3 => e (Geometry.localizeDerivation (T := F) (nonZeroDivisors P)
      (Geometry.invariantDerivation (biquadraticDirections a b i)))) =
      biquadraticDirections (algebraMap K F a) (algebraMap K F b) := by
    exact funext fun i =>
      (Geometry.fractionLogarithmicTangentEquiv_localize_invariantDerivation
        (biquadraticDirections a b i)).trans (map_biquadraticDirections (algebraMap K F) a b i)
  apply LinearIndependent.of_comp e.toLinearMap
  change LinearIndependent F (fun i : Fin 3 => e (Geometry.localizeDerivation (T := F)
    (nonZeroDivisors P) (Geometry.invariantDerivation (biquadraticDirections a b i))))
  rw [hdirs]
  exact biquadraticDirections_linearIndependent hma hmb

noncomputable def biquadraticFunctionFieldDerivationBasis
    {K : Type*} [Field K] [CharZero K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.Basis (Fin 3) (FractionRing (MvPolynomial (Fin 4) K))
      (LinearMap.ker (Geometry.fractionLogarithmicContractionLinearMap
        (biquadraticCoefficients a b))) :=
  (Module.Basis.span (biquadratic_functionField_derivations_linearIndependent ha hb)).map
    (LinearEquiv.ofEq _ _ (biquadratic_functionField_derivations_span_eq_ker ha hb))

 theorem coe_biquadraticFunctionFieldDerivationBasis
    {K : Type*} [Field K] [CharZero K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (i : Fin 3) :
    (biquadraticFunctionFieldDerivationBasis ha hb i :
      Derivation K (FractionRing (MvPolynomial (Fin 4) K)) (FractionRing (MvPolynomial (Fin 4) K))) =
      Geometry.localizeDerivation (nonZeroDivisors (MvPolynomial (Fin 4) K))
        (Geometry.invariantDerivation (biquadraticDirections a b i)) := by
  simp [biquadraticFunctionFieldDerivationBasis]

end WeightedTorusJets

end

end SiegelZeros

end OAI
