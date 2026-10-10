import OAI.Analysis.IrrationalRotation.Model.ProductBase
import OAI.Analysis.IrrationalRotation.Model.FieldDiagonal
import OAI.Analysis.IrrationalRotation.Model.GeneratedVonNeumann
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.Floor

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Invariant233.ProductModel

theorem measurable_rep : Measurable circleRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (T := (1 : ℝ)) 0).measurable

theorem measurable_iterate (θ : ℕ → ℝ) (k : ℤ) :
    Measurable (rotationIterate θ k) := by
  let : T0Space ℝ := @MetricSpace.instT0Space ℝ Real.metricSpace
  let : BorelSpace Circle := QuotientAddGroup.borelSpace
  let : ContinuousAdd Circle :=
    (QuotientAddGroup.instIsTopologicalAddGroup (AddSubgroup.zmultiples (1 : ℝ))).toContinuousAdd
  let : MeasurableAdd Circle := ContinuousAdd.measurableAdd
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply i).add_const _

theorem measurable_cost (θ c : ℕ → ℝ) : Measurable (logarithmicCost θ c) := by
  apply Measurable.tsum
  intro i
  have hm : Measurable (fun x : Base => circleRepresentative (x i) + θ i) :=
    (measurable_rep.comp (measurable_pi_apply i)).add_const (θ i)
  have hc : Measurable (fun x : Base => (⌊circleRepresentative (x i) + θ i⌋ : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp hm.floor
  exact (measurable_const.mul hc).ennreal_ofReal

theorem weight_measurable (θ c : ℕ → ℝ) : Measurable (weight θ c) := by
  exact (measurable_cost θ c).coe_ereal_ennreal.neg.ereal_exp.ennreal_toReal

theorem weight_nonneg (θ c : ℕ → ℝ) (x : Base) : 0 ≤ weight θ c x :=
  ENNReal.toReal_nonneg

theorem weight_le_one (θ c : ℕ → ℝ) (x : Base) : weight θ c x ≤ 1 := by
  have h : EReal.exp (-(logarithmicCost θ c x : EReal)) ≤ 1 := by
    rw [← EReal.exp_zero]
    apply EReal.exp_le_exp_iff.mpr
    exact EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg (logarithmicCost θ c x))
  exact (ENNReal.toReal_mono (by simp) h).trans (by simp)

def shiftOperator : Hilbert →L[ℂ] Hilbert :=
  (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap.compLpL 2 baseMeasure

def multiplierField (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ)
    (hb : ∀ x, ‖g x‖ ≤ C) (x : Base) : WeightedShift.Weight :=
  ⟨fun k => g (rotationIterate θ k x), memℓp_infty <| by
    refine ⟨C, ?_⟩
    rintro r ⟨k, rfl⟩
    exact hb _⟩

def multiplier (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) : Hilbert →L[ℂ] Hilbert :=
  WeightedShift.fieldDiagonal (multiplierField θ g C hb) C hC
    (fun _x => lp.norm_le_of_forall_le hC (fun _k => hb _))
    (fun k => (hg.comp (measurable_iterate θ k)).aestronglyMeasurable)

def multiplierGenerators (θ : ℕ → ℝ) : Set (Hilbert →L[ℂ] Hilbert) :=
  {A | ∃ (g : Base → ℂ) (C : ℝ) (hC : 0 ≤ C) (hg : Measurable g)
    (hb : ∀ x, ‖g x‖ ≤ C), A = multiplier θ g C hC hg hb}

def factor (θ : ℕ → ℝ) : VonNeumannAlgebra Hilbert :=
  vonNeumannGenerated ({shiftOperator} ∪ multiplierGenerators θ)

def traceVector : Hilbert := Lp.const 2 baseMeasure (lp.single 2 0 (1 : ℂ))

theorem measurable_complexWeight (θ c : ℕ → ℝ) :
    Measurable (fun x => (weight θ c x : ℂ)) :=
  (weight_measurable θ c).complex_ofReal

theorem norm_complexWeight_le_one (θ c : ℕ → ℝ) (x : Base) :
    ‖(weight θ c x : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg θ c x)]
    using weight_le_one θ c x

local instance instNormedAddCommGroupProductWeightedOperator : NormedAddCommGroup Hilbert :=
  @MeasureTheory.Lp.instNormedAddCommGroup Base Fiber MeasurableSpace.pi 2 baseMeasure
    (@lp.normedAddCommGroup ℤ (fun _ => ℂ) 2
      (fun _ => Complex.instNormedAddCommGroup) fact_one_le_two_ennreal)
    fact_one_le_two_ennreal

local instance instInnerProductSpaceProductWeightedOperator :
    @InnerProductSpace ℂ Hilbert Complex.instRCLike
      instNormedAddCommGroupProductWeightedOperator.toSeminormedAddCommGroup :=
  @MeasureTheory.L2.innerProductSpace Base Fiber ℂ Complex.instRCLike MeasurableSpace.pi
    baseMeasure
    (@lp.normedAddCommGroup ℤ (fun _ => ℂ) 2
      (fun _ => Complex.instNormedAddCommGroup) fact_one_le_two_ennreal)
    (@lp.instInnerProductSpace ℤ ℂ Complex.instRCLike (fun _ => ℂ)
      (fun _ => Complex.instNormedAddCommGroup)
      (fun _ => @RCLike.innerProductSpace ℂ Complex.instRCLike))

local instance instTopologicalSpaceProductWeightedOperator : TopologicalSpace Hilbert :=
  instNormedAddCommGroupProductWeightedOperator.toUniformSpace.toTopologicalSpace

local instance instAddCommMonoidProductWeightedOperator : AddCommMonoid Hilbert :=
  instNormedAddCommGroupProductWeightedOperator.toAddCommGroup.toAddCommMonoid

local instance instModuleProductWeightedOperator : Module ℂ Hilbert :=
  instInnerProductSpaceProductWeightedOperator.toNormedSpace.toModule

local notation "weightedOperatorSemiring" =>
  Complex.instNormedField.toField.toCommRing.toRing.toSemiring

local notation "weightedOperatorScalarIdentity" =>
  @RingHom.id ℂ (@Semiring.toNonAssocSemiring ℂ weightedOperatorSemiring)

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

def weightedOperator (θ c : ℕ → ℝ) :
    @ContinuousLinearMap ℂ ℂ weightedOperatorSemiring weightedOperatorSemiring
      weightedOperatorScalarIdentity
      Hilbert instTopologicalSpaceProductWeightedOperator instAddCommMonoidProductWeightedOperator
      Hilbert instTopologicalSpaceProductWeightedOperator instAddCommMonoidProductWeightedOperator
      instModuleProductWeightedOperator instModuleProductWeightedOperator :=
  let compose := fun (Scalar : Type) [Semiring Scalar] (Space : Type)
      [TopologicalSpace Space] [AddCommMonoid Space] [Module Scalar Space]
      (left right : Space →L[Scalar] Space) => left ∘L right
  @compose ℂ weightedOperatorSemiring Hilbert instTopologicalSpaceProductWeightedOperator
    instAddCommMonoidProductWeightedOperator instModuleProductWeightedOperator
    shiftOperator (multiplier θ (fun x => (weight θ c x : ℂ)) 1 zero_le_one
      (measurable_complexWeight θ c) (norm_complexWeight_le_one θ c))

end Invariant233.ProductModel

end

end OAI
