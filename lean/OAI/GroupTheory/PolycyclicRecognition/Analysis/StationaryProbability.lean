import OAI.GroupTheory.Thompson.InvariantMean
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Group.Action
import Mathlib.Topology.Algebra.ConstMulAction

namespace OAI

/-! # Invariant probability on a compact space of maps

The orbit average of an actual invariant mean is a positive functional on
compactly supported continuous functions. Its Riesz measure is a regular
probability and is invariant under the given action. No invariant measure is
postulated in this construction.
-/

noncomputable section

open MeasureTheory Set
open scoped CompactlySupported ENNReal

namespace PolycyclicRecognition

open ThompsonNonamenability

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]

/-- Restrict a bounded continuous function to an orbit, as an actual bounded
function on the acting group. -/
def boundedOrbit (x : X) (f : C_c(X, ℝ)) : BoundedReal G :=
  ⟨fun g => f (g • x), memℓp_infty ⟨‖f.toBoundedContinuousFunction‖, by
    rintro y ⟨g, rfl⟩
    exact f.toBoundedContinuousFunction.norm_coe_le_norm (g • x)⟩⟩

@[simp] theorem boundedOrbit_apply (x : X) (f : C_c(X, ℝ)) (g : G) :
    boundedOrbit x f g = f (g • x) := rfl

/-- The positive orbit-average functional. -/
def orbitAverage (M : InvariantMean G) (x : X) : C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toFun f := M (boundedOrbit x f)
  map_add' f k := by
    change M (boundedOrbit x (f + k)) = _
    rw [show boundedOrbit x (f + k) = boundedOrbit x f + boundedOrbit x k from
      lp.ext (funext fun _ => rfl), M.map_add]
  map_smul' r f := by
    change M (boundedOrbit x (r • f)) = _
    rw [show boundedOrbit x (r • f) = r • boundedOrbit x f from
      lp.ext (funext fun _ => rfl), M.map_smul]
    rfl
  monotone' f k h := M.mono (fun g => h (g • x))

variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

/-- The regular Riesz measure associated with the invariant orbit average. -/
def orbitProbability (M : InvariantMean G) (x : X) : Measure X :=
  RealRMK.rieszMeasure (orbitAverage M x)

instance orbitProbability_regular (M : InvariantMean G) (x : X) :
    (orbitProbability M x).Regular :=
  inferInstanceAs (RealRMK.rieszMeasure (orbitAverage M x)).Regular

instance orbitProbability_finite (M : InvariantMean G) (x : X) :
    IsFiniteMeasure (orbitProbability M x) :=
  inferInstanceAs (IsFiniteMeasure (RealRMK.rieszMeasure (orbitAverage M x)))

@[simp] theorem integral_orbitProbability (M : InvariantMean G) (x : X)
    (f : C_c(X, ℝ)) :
    ∫ y, f y ∂orbitProbability M x = M (boundedOrbit x f) :=
  RealRMK.integral_rieszMeasure _ _

instance orbitProbability_probability (M : InvariantMean G) (x : X) :
    IsProbabilityMeasure (orbitProbability M x) := by
  apply isProbabilityMeasure_iff_real.mpr
  let one : C_c(X, ℝ) := ⟨1, HasCompactSupport.of_compactSpace 1⟩
  have h := integral_orbitProbability M x one
  have ho : boundedOrbit (G := G) x one = 1 := lp.ext (funext fun _ => rfl)
  rw [ho, M.normalized] at h
  change (∫ _ : X, (1 : ℝ) ∂orbitProbability M x) = 1 at h
  simpa only [integral_const, smul_eq_mul, mul_one] using h

variable [ContinuousConstSMul G X]

/-- Every group element preserves the orbit-average probability. -/
theorem orbitProbability_map_smul (M : InvariantMean G) (x : X) (g : G) :
    Measure.map (g • ·) (orbitProbability M x) = orbitProbability M x := by
  let μ := orbitProbability M x
  have : (Measure.map (g • ·) μ).Regular :=
    Measure.Regular.map (Homeomorph.smul g)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let fg : C_c(X, ℝ) :=
    ⟨⟨fun y => f (g • y), f.continuous.comp (continuous_const_smul g)⟩,
      HasCompactSupport.of_compactSpace _⟩
  calc
    ∫ y, f y ∂Measure.map (g • ·) μ = ∫ y, fg y ∂μ :=
      integral_map (continuous_const_smul g).measurable.aemeasurable
        f.continuous.aestronglyMeasurable
    _ = M (boundedOrbit x fg) := integral_orbitProbability M x fg
    _ = M (leftPull g (boundedOrbit x f)) := by
      congr 1
      apply lp.ext
      funext h
      exact congrArg f (mul_smul g h x).symm
    _ = M (boundedOrbit x f) := M.left_invariant g _
    _ = ∫ y, f y ∂μ := (integral_orbitProbability M x f).symm

instance orbitProbability_invariant (M : InvariantMean G) (x : X) :
    SMulInvariantMeasure G X (orbitProbability M x) where
  measure_preimage_smul g s hs := by
    rw [← Measure.map_apply (continuous_const_smul g).measurable hs,
      orbitProbability_map_smul]

/-- Amenability supplies a regular invariant probability on every nonempty
compact Hausdorff action space. -/
theorem exists_invariant_probability (M : InvariantMean G) [Nonempty X] :
    ∃ μ : Measure X, μ.Regular ∧ IsProbabilityMeasure μ ∧ SMulInvariantMeasure G X μ := by
  obtain ⟨x⟩ := ‹Nonempty X›
  exact ⟨orbitProbability M x, inferInstance, inferInstance, inferInstance⟩

end PolycyclicRecognition

end

end OAI
