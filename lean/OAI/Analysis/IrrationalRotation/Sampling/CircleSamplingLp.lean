import OAI.Analysis.IrrationalRotation.Sampling.CircleSamplingKernelBridge

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.CircleParameterData

theorem kernel_bounds {m : ℕ} (hm : 0 < m) (z v : ℝ) :
    0 ≤ kernel m z v ∧ kernel m z v ≤ (m : ℝ)^2 / kernelWidth m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsq : (0 : ℝ) < (m : ℝ)^2 := sq_pos_of_pos hmR
  have hw : 0 < kernelWidth m := Real.rpow_pos_of_pos hmR _
  unfold kernel
  split_ifs with h
  · have hd : 0 < delta z := (one_div_pos.mpr hsq).trans_le h.1
    refine ⟨by positivity, ?_⟩
    calc
      1 / (kernelWidth m * delta z) ≤
          1 / (kernelWidth m * (1 / (m : ℝ)^2)) :=
        one_div_le_one_div_of_le (mul_pos hw (one_div_pos.mpr hsq))
          (mul_le_mul_of_nonneg_left h.1 hw.le)
      _ = (m : ℝ)^2 / kernelWidth m := by field_simp
  · exact ⟨le_rfl, by positivity⟩

theorem orientedKernel_bounds (endpoint : Bool) {m : ℕ} (hm : 0 < m) (z v : ℝ) :
    0 ≤ orientedKernel endpoint m z v ∧
      orientedKernel endpoint m z v ≤ (m : ℝ)^2 / kernelWidth m := by
  cases endpoint
  · exact kernel_bounds hm z v
  · exact kernel_bounds hm (z - v) v

theorem samplingAverage_bounds (p : CircleParameterData) (θ : ℝ) (j r : ℕ)
    (endpoint : Bool) (hm : 0 < p.m j) (x : Circle) :
    0 ≤ p.samplingAverage θ j r endpoint x ∧
      p.samplingAverage θ j r endpoint x ≤
        ((p.m j : ℝ)^2 / kernelWidth (p.m j)) ^ (p.block j).card := by
  classical
  have hb : 0 ≤ (p.m j : ℝ)^2 / kernelWidth (p.m j) := by
    exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hprod (n : ℕ) :
      0 ≤ ∏ i ∈ p.block j, orientedKernel endpoint (p.m j) (p.coordinate i x)
        (Int.fract ((n : ℝ) * p.alpha θ i)) := by
    exact Finset.prod_nonneg fun i _ => (orientedKernel_bounds endpoint hm _ _).1
  have hprod_le (n : ℕ) :
      (∏ i ∈ p.block j, orientedKernel endpoint (p.m j) (p.coordinate i x)
        (Int.fract ((n : ℝ) * p.alpha θ i))) ≤
        ((p.m j : ℝ)^2 / kernelWidth (p.m j)) ^ (p.block j).card := by
    calc
      _ ≤ ∏ _i ∈ p.block j, (p.m j : ℝ)^2 / kernelWidth (p.m j) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact (orientedKernel_bounds endpoint hm _ _).1
        · intro i hi
          exact (orientedKernel_bounds endpoint hm _ _).2
      _ = _ := by simp [div_pow]
  unfold samplingAverage
  refine ⟨mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => hprod n), ?_⟩
  by_cases hs : (p.samples j r).card = 0
  · simp only [hs, Nat.cast_zero, div_zero, zero_mul]
    exact pow_nonneg hb _
  · have hsR : ((p.samples j r).card : ℝ) ≠ 0 := by exact_mod_cast hs
    calc
      _ ≤ (1 / ((p.samples j r).card : ℝ)) *
          ∑ _n ∈ p.samples j r,
            ((p.m j : ℝ)^2 / kernelWidth (p.m j)) ^ (p.block j).card := by
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => hprod_le n)
        positivity
      _ = _ := by simp [hsR]

theorem memLp_samplingAverage (p : CircleParameterData) (θ : ℝ) (j r : ℕ)
    (endpoint : Bool) (hm : 0 < p.m j) (s : ENNReal) :
    MemLp (p.samplingAverage θ j r endpoint) s circleMeasure := by
  let : IsFiniteMeasure circleMeasure := by
    unfold circleMeasure
    infer_instance
  apply MemLp.of_bound (p.measurable_samplingAverage θ j r endpoint).aestronglyMeasurable
    (((p.m j : ℝ)^2 / kernelWidth (p.m j)) ^ (p.block j).card)
  apply Filter.Eventually.of_forall
  intro x
  have h := p.samplingAverage_bounds θ j r endpoint hm x
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

theorem memLp_samplingError (p : CircleParameterData) (θ : ℝ) (j r : ℕ)
    (endpoint : Bool) (hm : 0 < p.m j) (s : ENNReal) :
    MemLp (fun x => p.samplingAverage θ j r endpoint x - 1) s circleMeasure := by
  let : IsFiniteMeasure circleMeasure := by
    unfold circleMeasure
    infer_instance
  exact (p.memLp_samplingAverage θ j r endpoint hm s).sub (memLp_const (1 : ℝ))

end Invariant233.CircleParameterData

end

end OAI
