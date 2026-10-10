import OAI.Analysis.Pureness.Quasitrace.QuasitraceMetricContinuity
import OAI.Analysis.Pureness.Quasitrace.QuasitraceSqrtAddition

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace
open scoped NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (T : CuntzPureness.PositiveQuasitrace D) (c : ℝ≥0)

def scale : CuntzPureness.PositiveQuasitrace D where
  toFun a := (c : ℝ)*T a
  nonneg a := mul_nonneg c.2 (T.nonneg a)
  map_zero := by rw [T.map_zero,mul_zero]
  map_add_commute a b hab := by rw [T.map_add_commute a b hab,mul_add]
  map_smul r a := by rw [T.map_smul]; ring
  polar x := congrArg ((c : ℝ)*·) (T.polar x)
  monotone := fun _ _ h => mul_le_mul_of_nonneg_left (T.monotone h) c.2

lemma scale_metricSize (x : D) :
    (T.scale c).metricSize x = (c : ℝ)^((3:ℝ)⁻¹)*T.metricSize x :=
  Real.mul_rpow c.2 (T.nonneg _)

lemma scale_metricSize_add
    (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y) (x y : D) :
    (T.scale c).metricSize (x+y) ≤ (T.scale c).metricSize x+(T.scale c).metricSize y := by
  simp only [T.scale_metricSize, ← mul_add]
  exact mul_le_mul_of_nonneg_left (hadd x y) (Real.rpow_nonneg c.2 _)

lemma scale_sqrt_add
    (hsqrt : ∀ a b, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))
    (a b : Positive D) :
    Real.sqrt ((T.scale c) (Positive.add a b)) ≤
      Real.sqrt ((T.scale c) a)+Real.sqrt ((T.scale c) b) := by
  change Real.sqrt ((c : ℝ)*T (Positive.add a b)) ≤
    Real.sqrt ((c : ℝ)*T a)+Real.sqrt ((c : ℝ)*T b)
  calc
    _ = Real.sqrt (c : ℝ)*Real.sqrt (T (Positive.add a b)) := Real.sqrt_mul c.2 _
    _ ≤ Real.sqrt (c : ℝ)*(Real.sqrt (T a)+Real.sqrt (T b)) :=
      mul_le_mul_of_nonneg_left (hsqrt a b) (Real.sqrt_nonneg _)
    _ = Real.sqrt (c : ℝ)*Real.sqrt (T a)+Real.sqrt (c : ℝ)*Real.sqrt (T b) := mul_add _ _ _
    _ = _ := congrArg₂ (·+·) (Real.sqrt_mul c.2 (T a)).symm (Real.sqrt_mul c.2 (T b)).symm

lemma scale_selfAdjointValue (a : selfAdjoint D) :
    (T.scale c).selfAdjointValue a = (c : ℝ)*T.selfAdjointValue a := by
  change (c : ℝ)*T ⟨a.1⁺,_⟩-(c : ℝ)*T ⟨a.1⁻,_⟩ = _
  exact (mul_sub _ _ _).symm

lemma scale_complexValue (x : D) :
    (T.scale c).complexValue x = (c : ℂ)*T.complexValue x := by
  simp only [complexValue, T.scale_selfAdjointValue, Complex.ofReal_mul]
  ring

lemma normalize_unit (hu : 0 < T ⟨1,zero_le_one⟩) :
    (T.scale ⟨(T ⟨1,zero_le_one⟩)⁻¹, inv_nonneg.mpr hu.le⟩) ⟨1,zero_le_one⟩ = 1 :=
  inv_mul_cancel₀ hu.ne'
end CuntzPureness.PositiveQuasitrace

end

end OAI
