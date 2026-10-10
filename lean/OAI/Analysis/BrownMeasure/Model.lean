import Mathlib
import OAI.Analysis.FiniteFactor.CrossedProduct.VacuumFunctional

namespace OAI

section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology ENNReal CStarAlgebra
noncomputable section
namespace FiniteFactor
local instance : IsometricContinuousFunctionalCalculus ℝ
    (SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
instance productHilbertNontrivial : Nontrivial (SourceHilbert SourceCoordinate) := by
  have hv : sourceVacuum≠0 := by
    intro hz
    have h := sourceVacuum_norm
    rw [hz,norm_zero] at h
    norm_num at h
  exact ⟨⟨sourceVacuum,0,hv⟩⟩

end FiniteFactor
end
end

section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology
noncomputable section
namespace FiniteFactor
local notation "productMeasurable" =>
  @Prod.instMeasurableSpace (SourceCoordinate → ℝ) ℤ
    (@MeasurableSpace.pi SourceCoordinate (fun _ => ℝ)
      (fun _ => Real.measurableSpace)) Int.instMeasurableSpace
local notation "productSemiring" =>
  Complex.instNormedField.toField.toCommRing.toRing.toSemiring
local notation "productIdentity" =>
  @RingHom.id ℂ (@Semiring.toNonAssocSemiring ℂ productSemiring)
local notation "productExponent" =>
  @Nat.cast ENNReal
    (ENNReal.instAddCommMonoidWithOne.toAddMonoidWithOne.toNatCast)
    (Nat.succ (Nat.succ Nat.zero))
local notation "productHilbertGroup" =>
  @MeasureTheory.Lp.instNormedAddCommGroup
    ((SourceCoordinate → ℝ) × ℤ) ℂ productMeasurable
    productExponent
    (sourceMeasure SourceCoordinate) Complex.instNormedAddCommGroup
    fact_one_le_two_ennreal
local notation "productHilbertInner" =>
  @MeasureTheory.L2.innerProductSpace
    ((SourceCoordinate → ℝ) × ℤ) ℂ ℂ Complex.instRCLike
    productMeasurable (sourceMeasure SourceCoordinate)
    Complex.instNormedAddCommGroup (@RCLike.innerProductSpace ℂ Complex.instRCLike)
local notation "productHilbertTopology" =>
  @UniformSpace.toTopologicalSpace (SourceHilbert SourceCoordinate)
    (@PseudoMetricSpace.toUniformSpace (SourceHilbert SourceCoordinate)
      (@MetricSpace.toPseudoMetricSpace (SourceHilbert SourceCoordinate)
        (@NormedAddCommGroup.toMetricSpace (SourceHilbert SourceCoordinate) productHilbertGroup)))
local notation "productHilbertAddition" =>
  @AddCommGroup.toAddCommMonoid (SourceHilbert SourceCoordinate)
    (@NormedAddCommGroup.toAddCommGroup (SourceHilbert SourceCoordinate) productHilbertGroup)
local notation "productHilbertModule" =>
  @NormedSpace.toModule ℂ (SourceHilbert SourceCoordinate)
    (@DenselyNormedField.toNormedField ℂ
      (@RCLike.toDenselyNormedField ℂ Complex.instRCLike))
    (@NormedAddCommGroup.toSeminormedAddCommGroup
      (SourceHilbert SourceCoordinate) productHilbertGroup)
    (@InnerProductSpace.toNormedSpace ℂ (SourceHilbert SourceCoordinate) Complex.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup
        (SourceHilbert SourceCoordinate) productHilbertGroup)
      productHilbertInner)

abbrev ProductOp :=
  @ContinuousLinearMap ℂ ℂ productSemiring productSemiring productIdentity
    (SourceHilbert SourceCoordinate) productHilbertTopology productHilbertAddition
    (SourceHilbert SourceCoordinate) productHilbertTopology productHilbertAddition
    productHilbertModule productHilbertModule

section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology ENNReal
local instance : Module ℝ ProductOp := Module.complexToReal ProductOp
local instance : IsometricContinuousFunctionalCalculus ℝ ProductOp IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

def logarithmCutoff (n : ℕ) : C(ℝ,ℝ) where
  toFun t := Real.log (max (Real.exp (-(n:ℝ))) t)
  continuous_toFun := (continuous_const.max continuous_id).log
    (fun _=>ne_of_gt ((Real.exp_pos _).trans_le (le_max_left _ _)))

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def FugledeKadisonDeterminant (τ : ProductOp → ℂ) (T : ProductOp) : ℝ≥0∞ :=
  let determinant := fun (Hilbert : Type) [NormedAddCommGroup Hilbert]
    [InnerProductSpace ℂ Hilbert] [CompleteSpace Hilbert] [Nontrivial Hilbert]
    (trace : (Hilbert →L[ℂ] Hilbert) → ℂ) (operator : Hilbert →L[ℂ] Hilbert) =>
      letI : Module ℝ (Hilbert →L[ℂ] Hilbert) := Module.complexToReal _
      letI : IsometricContinuousFunctionalCalculus ℝ (Hilbert →L[ℂ] Hilbert)
          IsSelfAdjoint := IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
      ⨅ n : ℕ, ENNReal.ofReal
        (Real.exp ((trace (cfc (logarithmCutoff n) (CFC.abs operator))).re))
  let domain := (SourceCoordinate → ℝ) × ℤ
  let measurable : MeasurableSpace domain := productMeasurable
  let exponent : ℝ≥0∞ := productExponent
  let measure : @Measure domain measurable := sourceMeasure SourceCoordinate
  let complete := @MeasureTheory.Lp.instCompleteSpace domain measurable exponent measure ℂ
    Complex.instNormedAddCommGroup Complex.instCompleteSpace fact_one_le_two_ennreal
  @determinant (SourceHilbert SourceCoordinate) productHilbertGroup productHilbertInner
    complete productHilbertNontrivial τ T

end

section
open MeasureTheory Filter
open scoped ENNReal Topology

def expLogPotential (μ : Measure ℂ) (z : ℂ) : ℝ≥0∞ :=
  ⨅ n : ℕ, ENNReal.ofReal (Real.exp (∫ w,logarithmCutoff n ‖z-w‖ ∂μ))

def IsBrownMeasure (τ : ProductOp → ℂ) (T : ProductOp) (μ : Measure ℂ) : Prop :=
  let translate := fun (Hilbert : Type) [NormedAddCommGroup Hilbert]
    [NormedSpace ℂ Hilbert] (operator : Hilbert →L[ℂ] Hilbert) (scalar : ℂ) =>
      operator - algebraMap ℂ (Hilbert →L[ℂ] Hilbert) scalar
  IsProbabilityMeasure μ ∧ IsCompact μ.support ∧
  ∀ z : ℂ, FugledeKadisonDeterminant τ
    (@translate (SourceHilbert SourceCoordinate) productHilbertGroup
      (@InnerProductSpace.toNormedSpace ℂ (SourceHilbert SourceCoordinate) Complex.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup
          (SourceHilbert SourceCoordinate) productHilbertGroup)
        productHilbertInner) T z) = expLogPotential μ z

def ProductBrownClaim : Prop :=
  ∀ (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ),
    IsBrownMeasure sourceVacuumFunctional
      (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg) (Measure.dirac 0)

end

end FiniteFactor
end
end

end OAI
