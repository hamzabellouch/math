import Mathlib
import OAI.Analysis.FiniteFactor.CrossedProduct.GeneratedAlgebra
import OAI.Analysis.FiniteFactor.OperatorUltraweak

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- The constant e_0 field in the actual L2(X times Z) source model. -/
def sourceVacuum : SourceHilbert SourceCoordinate :=
  @indicatorConstLp ((SourceCoordinate → ℝ) × ℤ) ℂ
    (@Prod.instMeasurableSpace (SourceCoordinate → ℝ) ℤ
      (@MeasurableSpace.pi SourceCoordinate (fun _ => ℝ)
        (fun _ => Real.measurableSpace)) Int.instMeasurableSpace)
    (sourceMeasure SourceCoordinate) Complex.instNormedAddCommGroup
    (Set.univ ×ˢ {(0 : ℤ)})
    (@Nat.cast ENNReal
      (ENNReal.instAddCommMonoidWithOne.toAddMonoidWithOne.toNatCast)
      (Nat.succ (Nat.succ Nat.zero)))
    (MeasurableSet.univ.prod (measurableSet_singleton (0 : ℤ)))
    (letI : IsProbabilityMeasure unitIntervalMeasure :=
       ⟨(Measure.restrict_apply_univ
           (μ := (volume : Measure ℝ)) (Set.Ico (0 : ℝ) 1)).trans
         ((Real.volume_Ico (a := 0) (b := 1)).trans
           ((congrArg ENNReal.ofReal (sub_zero (1 : ℝ))).trans
             ENNReal.ofReal_one))⟩
     let base : Measure (SourceCoordinate → ℝ) :=
       Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)
     let mass_one :=
       (Measure.prod_prod (μ := base) (ν := (Measure.count : Measure ℤ))
         Set.univ {(0 : ℤ)}).trans
         ((congrArg₂ (fun left right : ℝ≥0∞ => left * right)
           (measure_univ (μ := base))
           (Measure.count_singleton (0 : ℤ))).trans (one_mul (1 : ℝ≥0∞)))
     fun mass_top => ENNReal.one_ne_top (mass_one.symm.trans mass_top)) (1 : ℂ)

theorem sourceVacuum_norm : ‖sourceVacuum‖ = 1 := by
  rw [sourceVacuum,norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp [measureReal_def,sourceMeasure,Measure.prod_prod]

section

local notation "vacuumMeasurable" =>
  @Prod.instMeasurableSpace (SourceCoordinate → ℝ) ℤ
    (@MeasurableSpace.pi SourceCoordinate (fun _ => ℝ)
      (fun _ => Real.measurableSpace)) Int.instMeasurableSpace
local notation "vacuumSemiring" =>
  Complex.instNormedField.toField.toCommRing.toRing.toSemiring
local notation "vacuumIdentity" =>
  @RingHom.id ℂ (@Semiring.toNonAssocSemiring ℂ vacuumSemiring)
local notation "vacuumHilbertGroup" =>
  @MeasureTheory.Lp.instNormedAddCommGroup
    ((SourceCoordinate → ℝ) × ℤ) ℂ vacuumMeasurable
    (@Nat.cast ENNReal
      (ENNReal.instAddCommMonoidWithOne.toAddMonoidWithOne.toNatCast)
      (Nat.succ (Nat.succ Nat.zero)))
    (sourceMeasure SourceCoordinate) Complex.instNormedAddCommGroup
    fact_one_le_two_ennreal
local notation "vacuumHilbertInner" =>
  @MeasureTheory.L2.innerProductSpace
    ((SourceCoordinate → ℝ) × ℤ) ℂ ℂ Complex.instRCLike
    vacuumMeasurable (sourceMeasure SourceCoordinate)
    Complex.instNormedAddCommGroup (@RCLike.innerProductSpace ℂ Complex.instRCLike)
local notation "vacuumHilbertTopology" =>
  @UniformSpace.toTopologicalSpace (SourceHilbert SourceCoordinate)
    (@PseudoMetricSpace.toUniformSpace (SourceHilbert SourceCoordinate)
      (@MetricSpace.toPseudoMetricSpace (SourceHilbert SourceCoordinate)
        (@NormedAddCommGroup.toMetricSpace (SourceHilbert SourceCoordinate) vacuumHilbertGroup)))
local notation "vacuumHilbertAddition" =>
  @AddCommGroup.toAddCommMonoid (SourceHilbert SourceCoordinate)
    (@NormedAddCommGroup.toAddCommGroup (SourceHilbert SourceCoordinate) vacuumHilbertGroup)
local notation "vacuumHilbertModule" =>
  @NormedSpace.toModule ℂ (SourceHilbert SourceCoordinate)
    (@DenselyNormedField.toNormedField ℂ
      (@RCLike.toDenselyNormedField ℂ Complex.instRCLike))
    (@NormedAddCommGroup.toSeminormedAddCommGroup
      (SourceHilbert SourceCoordinate) vacuumHilbertGroup)
    (@InnerProductSpace.toNormedSpace ℂ (SourceHilbert SourceCoordinate) Complex.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup
        (SourceHilbert SourceCoordinate) vacuumHilbertGroup)
      vacuumHilbertInner)

abbrev sourceVacuumFunctional
    (operator : @ContinuousLinearMap ℂ ℂ vacuumSemiring vacuumSemiring vacuumIdentity
      (SourceHilbert SourceCoordinate) vacuumHilbertTopology vacuumHilbertAddition
      (SourceHilbert SourceCoordinate) vacuumHilbertTopology vacuumHilbertAddition
      vacuumHilbertModule vacuumHilbertModule) : ℂ :=
  @inner ℂ (SourceHilbert SourceCoordinate)
    (@InnerProductSpace.toInner ℂ (SourceHilbert SourceCoordinate) Complex.instRCLike
      (@NormedAddCommGroup.toSeminormedAddCommGroup
        (SourceHilbert SourceCoordinate) vacuumHilbertGroup)
      vacuumHilbertInner) sourceVacuum
    (@AddHom.toFun (SourceHilbert SourceCoordinate) (SourceHilbert SourceCoordinate)
      (vacuumHilbertAddition).toAdd (vacuumHilbertAddition).toAdd
      (@LinearMap.toAddHom ℂ ℂ vacuumSemiring vacuumSemiring vacuumIdentity
        (SourceHilbert SourceCoordinate) (SourceHilbert SourceCoordinate)
        vacuumHilbertAddition vacuumHilbertAddition vacuumHilbertModule vacuumHilbertModule
        (@ContinuousLinearMap.toLinearMap ℂ ℂ vacuumSemiring vacuumSemiring vacuumIdentity
          (SourceHilbert SourceCoordinate) vacuumHilbertTopology vacuumHilbertAddition
          (SourceHilbert SourceCoordinate) vacuumHilbertTopology vacuumHilbertAddition
          vacuumHilbertModule vacuumHilbertModule operator)) sourceVacuum)

end

theorem sourceVacuumFunctional_one : sourceVacuumFunctional 1 = 1 := by
  simp [sourceVacuumFunctional,inner_self_eq_norm_sq_to_K,sourceVacuum_norm]

theorem sourceVacuumFunctional_add (S T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    sourceVacuumFunctional (S+T) = sourceVacuumFunctional S + sourceVacuumFunctional T := by
  simp [sourceVacuumFunctional,inner_add_right]

theorem sourceVacuumFunctional_smul (c : ℂ)
    (T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    sourceVacuumFunctional (c • T) = c * sourceVacuumFunctional T := by
  simp [sourceVacuumFunctional,inner_smul_right]

theorem sourceVacuumFunctional_bound
    (T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    ‖sourceVacuumFunctional T‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖sourceVacuum‖ * ‖T sourceVacuum‖ := norm_inner_le_norm _ _
    _ ≤ ‖sourceVacuum‖ * (‖T‖ * ‖sourceVacuum‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = _ := by rw [sourceVacuum_norm]; ring

theorem sourceVacuumFunctional_square
    (T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    sourceVacuumFunctional (star T*T) = inner ℂ (T sourceVacuum) (T sourceVacuum) :=
  ContinuousLinearMap.adjoint_inner_right T sourceVacuum (T sourceVacuum)

theorem sourceVacuumFunctional_square_nonneg
    (T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    0 ≤ (sourceVacuumFunctional (star T*T)).re := by
  rw [sourceVacuumFunctional_square]
  rw [inner_self_eq_norm_sq_to_K]
  exact_mod_cast sq_nonneg ‖T sourceVacuum‖

/-- Normality here is continuity for the actual ultraweak topology defined
by absolutely summable vector functionals, specialized to the source Hilbert space. -/
theorem sourceVacuumFunctional_normal :
    @Continuous _ _ (ultraweakTopology (SourceHilbert SourceCoordinate)) inferInstance sourceVacuumFunctional :=
  vectorFunctional_ultraweak_continuous sourceVacuum sourceVacuum

@[instance_reducible] def sourceAlgebraUltraweakTopology (θ : SourceCoordinate → ℝ) :
    TopologicalSpace (sourceAlgebra θ).toStarSubalgebra :=
  TopologicalSpace.induced (fun T : (sourceAlgebra θ).toStarSubalgebra =>
    (T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate))
    (ultraweakTopology (SourceHilbert SourceCoordinate))

theorem sourceVacuumFunctional_algebra_normal (θ : SourceCoordinate → ℝ) :
    @Continuous _ _ (sourceAlgebraUltraweakTopology θ) inferInstance
      (fun T : (sourceAlgebra θ).toStarSubalgebra => sourceVacuumFunctional T) :=
  @Continuous.comp _ _ _ (sourceAlgebraUltraweakTopology θ) (ultraweakTopology (SourceHilbert SourceCoordinate)) _ _ _
    sourceVacuumFunctional_normal continuous_induced_dom

end
end FiniteFactor

end OAI
