import OAI.Analysis.FiniteFactor.Sampling.Weights
import OAI.Analysis.FiniteFactor.OrbitSampling.Discrepancy

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset Filter
open scoped ENNReal
noncomputable section

def sourceSamplingWidth (s : ℕ) : ℝ := (sourceBlockSize s : ℝ)^(-3/5 : ℝ)
def sourceSamplingCutoff (s : ℕ) : ℝ := (sourceBlockSize s : ℝ)^(-2 : ℝ)
def sourceSamplingPrefix (s : ℕ) : Finset SourceCoordinate :=
  CouplingParameters.blockPrefix sourceBlockSize (s+1)

theorem sourceSampling_parameters (s : ℕ) :
    0 < sourceSamplingWidth s ∧ sourceSamplingWidth s < 1 ∧ 0 < sourceSamplingCutoff s := by
  have hm : (100 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_100
  refine ⟨by unfold sourceSamplingWidth; positivity, ?_, by unfold sourceSamplingCutoff; positivity⟩
  exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)

theorem sourceSampling_weight_bound (s : ℕ) (triangular : Bool) (x t : ℝ) :
    0 ≤ samplingWeight triangular (sourceSamplingWidth s) (sourceSamplingCutoff s) x t ∧
      samplingWeight triangular (sourceSamplingWidth s) (sourceSamplingCutoff s) x t ≤
        (sourceBlockSize s : ℝ)^(13/5 : ℝ) := by
  have hp := sourceSampling_parameters s
  have hb := samplingWeight_bounds triangular _ _ x t hp.1 hp.2.2
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hm := sourceBlockSize_pos s
  have hm1 : (1 : ℝ) ≤ sourceBlockSize s := by
    have hh : (100 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_100
    linarith
  apply max_le
  · exact Real.one_le_rpow hm1 (by norm_num)
  · unfold sourceSamplingWidth sourceSamplingCutoff
    rw [← Real.rpow_add hm]
    norm_num
    rw [Real.rpow_neg hm.le,inv_inv]

def sourceSamplingWeight (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) (x : SourceCoordinate → ℝ) : ℝ :=
  ∏ i ∈ sourceSamplingPrefix s,
    samplingWeight (decide (i ∈ I)) (sourceSamplingWidth s) (sourceSamplingCutoff s)
      (x i) (Int.fract ((n : ℝ)*θ i))

theorem sourceSamplingWeight_measurable (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) : Measurable (sourceSamplingWeight I s θ n) := by
  apply Finset.measurable_prod
  intro i hi
  have hp : Measurable (fun x : SourceCoordinate → ℝ => (x i, Int.fract ((n : ℝ)*θ i))) :=
    (measurable_pi_apply i).prodMk measurable_const
  exact (samplingWeight_measurable (decide (i ∈ I)) (sourceSamplingWidth s) (sourceSamplingCutoff s)).comp hp

theorem sourceSamplingWeight_bounds (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) (x : SourceCoordinate → ℝ) :
    0 ≤ sourceSamplingWeight I s θ n x ∧ sourceSamplingWeight I s θ n x ≤
      ((sourceBlockSize s : ℝ)^(13/5 : ℝ))^(sourceSamplingPrefix s).card := by
  constructor
  · exact prod_nonneg (fun i hi => (sourceSampling_weight_bound s _ _ _).1)
  · unfold sourceSamplingWeight
    calc
      _ ≤ ∏ _i ∈ sourceSamplingPrefix s, (sourceBlockSize s : ℝ)^(13/5 : ℝ) :=
        prod_le_prod₀ (fun i hi => (sourceSampling_weight_bound s _ _ _).1)
          (fun i hi => (sourceSampling_weight_bound s _ _ _).2)
      _ = _ := by simp

/-- Each actual finite-stage weight has an L2 density. This bound is for
one stage; it does not assert the later uniform-in-stage sampling bound. -/
theorem sourceSamplingWeight_memLp (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) :
    MemLp (sourceSamplingWeight I s θ n) 2
      (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) := by
  apply MemLp.of_bound (sourceSamplingWeight_measurable I s θ n).aestronglyMeasurable
    (((sourceBlockSize s : ℝ)^(13/5 : ℝ))^(sourceSamplingPrefix s).card)
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sourceSamplingWeight_bounds I s θ n x).1]
    exact (sourceSamplingWeight_bounds I s θ n x).2)

/-- The actual density depends only on the prefix, before tail trimming. -/
theorem sourceSamplingWeight_prefix (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) (x y : SourceCoordinate → ℝ)
    (hxy : ∀ i ∈ sourceSamplingPrefix s, x i = y i) :
    sourceSamplingWeight I s θ n x = sourceSamplingWeight I s θ n y := by
  apply prod_congr rfl
  intro i hi
  rw [hxy i hi]

/-- Every nonzero summand orders all prefix coordinates under the actual rotation. -/
theorem sourceSamplingWeight_orders_prefix (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) (x : SourceCoordinate → ℝ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) (hw : sourceSamplingWeight I s θ n x ≠ 0) :
    ∀ i ∈ sourceSamplingPrefix s, x i < coordinateRotate θ n x i := by
  intro i hi
  have hp := sourceSampling_parameters s
  have hwi := Finset.prod_ne_zero_iff.mp hw i hi
  have horder := (samplingWeight_orders (decide (i ∈ I)) _ _ (x i)
    (Int.fract ((n : ℝ)*θ i)) hp.1 hp.2.1 hp.2.2 (hx i) hwi).2
  have he : x i+(n : ℝ)*θ i = (x i+Int.fract ((n : ℝ)*θ i)) + (⌊(n : ℝ)*θ i⌋ : ℝ) := by
    linarith [Int.fract_add_floor ((n : ℝ)*θ i)]
  unfold coordinateRotate
  rw [he,Int.fract_add_intCast]
  exact horder

end
end FiniteFactor

end OAI
