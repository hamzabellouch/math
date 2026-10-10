import Mathlib
import OAI.Analysis.FiniteFactor.CrossedProduct.FloorSupport

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Integer iterates of the source rotation, in [0,1) representatives. -/
def coordinateRotate {ι : Type*} (θ : ι → ℝ) (k : ℤ) (x : ι → ℝ) (i : ι) : ℝ :=
  Int.fract (x i + (k : ℝ)*θ i)

theorem coordinateFloor_add {ι : Type*} (θ : ι → ℝ) (x : ι → ℝ) (k n : ℤ) (i : ι) :
    coordinateFloor θ (k+n) x i = coordinateFloor θ k x i +
      coordinateFloor θ n (coordinateRotate θ k x) i := by
  unfold coordinateFloor coordinateRotate
  have he : x i + ((k+n : ℤ) : ℝ)*θ i =
      (Int.fract (x i+(k : ℝ)*θ i)+(n : ℝ)*θ i) + (Int.floor (x i+(k : ℝ)*θ i) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [he, Int.floor_add_intCast]
  omega

theorem finiteFloorSupport_rotate {ι : Type*} (θ : ι → ℝ) {x : ι → ℝ}
    (hx : finiteFloorSupport θ x) (k : ℤ) : finiteFloorSupport θ (coordinateRotate θ k x) := by
  intro n
  apply ((hx (k+n)).union (hx k)).subset
  intro i hi
  by_contra hn
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
  have he := coordinateFloor_add θ x k n i
  rw [hn.1, hn.2, zero_add] at he
  exact hi he.symm

/-- The source logarithmic cocycle, using the actual weighted floor sum. -/
def sourceLog {ι : Type*} (θ c : ι → ℝ) (k : ℤ) (x : ι → ℝ) : ℝ :=
  ∑' i, c i * (coordinateFloor θ k x i : ℝ)

def sourceCocycle {ι : Type*} (θ c : ι → ℝ) (k : ℤ) (x : ι → ℝ) : ℝ :=
  Real.exp (-sourceLog θ c k x)

theorem sourceLog_summable {ι : Type*} (θ c : ι → ℝ) {x : ι → ℝ}
    (hx : finiteFloorSupport θ x) (k : ℤ) :
    Summable (fun i => c i * (coordinateFloor θ k x i : ℝ)) := by
  apply summable_of_hasFiniteSupport
  apply (hx k).subset
  intro i hi
  simp only [Function.mem_support] at *
  intro hz
  apply hi
  simp [hz]

theorem sourceLog_add {ι : Type*} (θ c : ι → ℝ) {x : ι → ℝ}
    (hx : finiteFloorSupport θ x) (k n : ℤ) :
    sourceLog θ c (k+n) x = sourceLog θ c k x + sourceLog θ c n (coordinateRotate θ k x) := by
  unfold sourceLog
  simp_rw [coordinateFloor_add, Int.cast_add, mul_add]
  exact (sourceLog_summable θ c hx k).tsum_add
    (sourceLog_summable θ c (finiteFloorSupport_rotate θ hx k) n)

/-- The actual cocycle identity, proved on the conull domain supplied by
Borel--Cantelli. The rotation and sums are explicit. -/
theorem sourceCocycle_add {ι : Type*} (θ c : ι → ℝ) {x : ι → ℝ}
    (hx : finiteFloorSupport θ x) (k n : ℤ) :
    sourceCocycle θ c (k+n) x = sourceCocycle θ c n (coordinateRotate θ k x) * sourceCocycle θ c k x := by
  rw [sourceCocycle, sourceLog_add θ c hx, neg_add, Real.exp_add]
  exact mul_comm _ _

theorem sourceCocycle_pos {ι : Type*} (θ c : ι → ℝ) (k : ℤ) (x : ι → ℝ) :
    0 < sourceCocycle θ c k x := Real.exp_pos _

theorem sourceCocycle_zero {ι : Type*} (θ c : ι → ℝ) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Ico 0 1) : sourceCocycle θ c 0 x = 1 := by
  have hzero (i : ι) : coordinateFloor θ 0 x i = 0 := by
    simpa [coordinateFloor] using Int.floor_eq_zero_iff.mpr (hx i)
  simp [sourceCocycle, sourceLog, hzero]

theorem sourceCocycle_measurable {ι : Type*} [Countable ι]
    (θ c : ι → ℝ) (k : ℤ) :
    @Measurable (ι → ℝ) ℝ
      (@MeasurableSpace.pi ι (fun _ => ℝ) (fun _ => Real.measurableSpace))
      Real.measurableSpace (sourceCocycle θ c k) := by
  apply Real.continuous_exp.measurable.comp
  apply Measurable.neg
  apply Measurable.tsum
  intro i
  have hm0 : Measurable (fun x : ι → ℝ => x i + (k : ℝ)*θ i) :=
    (measurable_pi_apply i).add measurable_const
  have hm := Int.measurable_floor.comp hm0
  exact measurable_const.mul ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp hm)

/-- The weight f=F_1 is positive and at most one on the source coordinate cube. -/
theorem sourceWeight_le_one {ι : Type*} (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Ico 0 1) : sourceCocycle θ c 1 x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  apply neg_nonpos.mpr
  apply tsum_nonneg
  intro i
  apply mul_nonneg (hc i)
  unfold coordinateFloor
  exact_mod_cast Int.floor_nonneg.mpr (show 0 ≤ x i + (1 : ℤ)*θ i by simpa using add_nonneg (hx i).1 (hθ i))

/-- Ordered endpoints give the ratio bound for every integer, including
negative integers. Both infinite sums are justified by finite support. -/
theorem sourceCocycle_ordered {ι : Type*} (θ c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) {x y : ι → ℝ}
    (hx : finiteFloorSupport θ x) (hy : finiteFloorSupport θ y)
    (hxy : ∀ i, x i ≤ y i) (k : ℤ) : sourceCocycle θ c k y ≤ sourceCocycle θ c k x := by
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact Summable.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_left
    (by
      have hh : coordinateFloor θ k x i ≤ coordinateFloor θ k y i :=
        Int.floor_mono (add_le_add (hxy i) le_rfl)
      exact_mod_cast hh) (hc i))
    (sourceLog_summable θ c hx k) (sourceLog_summable θ c hy k)

end
end FiniteFactor

end OAI
