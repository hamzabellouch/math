import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import OAI.NumberTheory.PiExponent.Analysis.LogarithmicObstruction
import OAI.NumberTheory.PiExponent.LocalAlgebra.TranscendenceBasisReduction

namespace OAI

noncomputable section

namespace PiExponent

open KaehlerDifferential
open scoped TensorProduct Polynomial nonZeroDivisors IntermediateField

def extendDerivation
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallyEtale S T]
    (d : Derivation R S S) : Derivation R T T :=
  ((LinearMap.liftBaseChange T ((Algebra.linearMap S T).comp d.liftKaehlerDifferential)).comp
    (tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer (D R T)

theorem extendDerivation_algebraMap
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallyEtale S T]
    (d : Derivation R S S) (s : S) :
    extendDerivation (T := T) d (algebraMap S T s) = algebraMap S T (d s) := by
  simp [extendDerivation, LinearMap.compDer,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Derivation.liftKaehlerDifferential_comp_D]

def ratFuncDerivative {K : Type*} [Field K] : Derivation K (RatFunc K) (RatFunc K) := by
  letI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (K[X]⁰)
  exact extendDerivation Polynomial.derivative'

@[simp]
theorem ratFuncDerivative_X {K : Type*} [Field K] :
    ratFuncDerivative (RatFunc.X : RatFunc K) = 1 := by
  let : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (K[X]⁰)
  change extendDerivation Polynomial.derivative' (RatFunc.X : RatFunc K) = 1
  rw [← RatFunc.algebraMap_X, extendDerivation_algebraMap]
  simp [Polynomial.derivative']

theorem finite_extension_no_logarithmic_differential
    {K E : Type*} [Field K] [CharZero K] [Field E]
    [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E] (x : E) :
    D K E x ≠ (algebraMap (RatFunc K) E RatFunc.X)⁻¹ •
      D K E (algebraMap (RatFunc K) E RatFunc.X) := by
  let : Algebra.FormallyEtale (RatFunc K) E :=
    Algebra.FormallyEtale.of_isSeparable (RatFunc K) E
  let delta : Derivation K E E := extendDerivation ratFuncDerivative
  have hcompat (a : RatFunc K) :
      delta (algebraMap (RatFunc K) E a) =
        algebraMap (RatFunc K) E (ratFuncDerivative a) :=
    extendDerivation_algebraMap ratFuncDerivative a
  intro heq
  have hd := congrArg delta.liftKaehlerDifferential heq
  simp only [Derivation.liftKaehlerDifferential_comp_D, map_smul, hcompat,
    ratFuncDerivative_X, map_one, smul_eq_mul, mul_one] at hd
  apply finite_extension_derivation_ne_simple_pole ratFuncDerivative delta
    ratFuncDerivative_X hcompat x (c := (1 : K)) one_ne_zero
  simpa only [map_div₀, map_one, one_div, map_inv₀] using hd

theorem adjoin_finite_no_logarithmic_differential
    {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]
    (y : E) (hy : Transcendental K y) [FiniteDimensional K⟮y⟯ E] (x : E) :
    D K E x ≠ y⁻¹ • D K E y := by
  let F := K⟮y⟯
  let e : RatFunc K ≃ₐ[K] F := RatFunc.algEquivOfTranscendental y hy
  let : Algebra (RatFunc K) F := e.toRingHom.toAlgebra
  let : Algebra (RatFunc K) E :=
    ((algebraMap F E).comp e.toRingHom).toAlgebra
  let : IsScalarTower (RatFunc K) F E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K (RatFunc K) E := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap K E a = algebraMap F E (e (algebraMap K (RatFunc K) a))
    rw [e.commutes]
    exact IsScalarTower.algebraMap_apply K F E a
  have : Module.Finite (RatFunc K) F :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) F) e.surjective
  have : Module.Finite (RatFunc K) E := Module.Finite.trans F E
  have hX : algebraMap (RatFunc K) E RatFunc.X = y := by
    change ((RatFunc.algEquivOfTranscendental y hy) RatFunc.X : E) = y
    exact RatFunc.algEquivOfTranscendental_X y hy
  simpa only [hX] using finite_extension_no_logarithmic_differential (K := K) x

theorem logarithmic_differential_base_change
    {C K E : Type*} [Field C] [Field K] [Field E]
    [Algebra C K] [Algebra C E] [Algebra K E] [IsScalarTower C K E]
    {x y : E} (h : D C E x = y⁻¹ • D C E y) :
    D K E x = y⁻¹ • D K E y := by
  have hm := congrArg (KaehlerDifferential.map C K E E) h
  simpa only [map_D, map_smul, Algebra.algebraMap_self, RingHom.id_apply] using hm

theorem no_logarithmic_differential_over_intermediateField
    {C E : Type*} [Field C] [CharZero C] [Field E] [Algebra C E]
    (K : IntermediateField C E) (y : E) (hy : Transcendental K y)
    [FiniteDimensional K⟮y⟯ E] (x : E) :
    D C E x ≠ y⁻¹ • D C E y := by
  intro h
  exact adjoin_finite_no_logarithmic_differential y hy x
    (logarithmic_differential_base_change (K := K) h)

theorem isAlgebraic_of_logarithmic_differential
    {C E : Type*} [Field C] [CharZero C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] (x y : E)
    (h : D C E x = y⁻¹ • D C E y) : IsAlgebraic C y := by
  by_contra hy
  obtain ⟨K, hKy, hfinite⟩ := exists_intermediateField_finite_over_simple C E hy
  have : FiniteDimensional K⟮y⟯ E := hfinite
  exact no_logarithmic_differential_over_intermediateField K y hKy x h

theorem constant_of_logarithmic_differential
    {C E : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] (x y : E)
    (h : D C E x = y⁻¹ • D C E y) : ∃ c : C, algebraMap C E c = y := by
  have hy := isAlgebraic_of_logarithmic_differential x y h
  have hmem : y ∈ algebraicClosure C E := mem_algebraicClosure_iff.mpr hy
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure C E)] at hmem
  exact IntermediateField.mem_bot.mp hmem

end PiExponent

end

end OAI
