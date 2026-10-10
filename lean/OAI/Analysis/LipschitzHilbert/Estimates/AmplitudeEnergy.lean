import OAI.Analysis.LipschitzHilbert.Estimates.FiniteRestrictedStrong
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! Actual disjoint amplitude levels and their square-energy budget. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

def amplitudeLevel (f : X → E) (i : ℤ) : Set X :=
  {x | (2:ℝ)^(i-1)<‖f x‖ ∧ ‖f x‖≤(2:ℝ)^i}

theorem amplitudeLevel_measurable {f : X → E} (hf : Measurable (fun x => ‖f x‖)) (i : ℤ) :
    MeasurableSet (amplitudeLevel f i) :=
  (measurableSet_lt measurable_const hf).inter (measurableSet_le hf measurable_const)

omit [MeasurableSpace X] in
theorem amplitudeLevel_disjoint (f : X → E) : Pairwise (fun i j => Disjoint (amplitudeLevel f i) (amplitudeLevel f j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have hp : (2:ℝ)^i≤(2:ℝ)^(j-1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    exact (not_lt_of_ge (hxi.2.trans hp)) hxj.1
  · have hp : (2:ℝ)^j≤(2:ℝ)^(i-1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    exact (not_lt_of_ge (hxj.2.trans hp)) hxi.1

theorem amplitudeLevel_finite (μ : Measure X) {f : X → E} (hf : MemLp f 2 μ) (i : ℤ) :
    μ (amplitudeLevel f i)≠∞ := by
  let eps : ℝ≥0 := ⟨(2:ℝ)^(i-1),(zpow_pos (by norm_num) _).le⟩
  have heps : eps≠0 := by
    intro h
    have := congrArg (fun t : ℝ≥0 => (t:ℝ)) h
    exact (zpow_pos (by norm_num : (0:ℝ)<2) (i-1)).ne' this
  have h := hf.meas_ge_lt_top (by norm_num) (by norm_num) heps
  apply ne_top_of_le_ne_top h.ne (measure_mono ?_)
  intro x hx
  exact_mod_cast hx.1.le

theorem amplitude_energy_budget (μ : Measure X) {f : X → E}
    (hf : MemLp f 2 μ) (hm : Measurable (fun x => ‖f x‖)) (I : Finset ℤ) :
    (∑ i∈I, ((2:ℝ)^i*Real.sqrt (μ.real (amplitudeLevel f i)))^2)≤
      4*(∫ x, ‖f x‖^2 ∂μ) := by
  have hsq := hf.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hlevel (i : ℤ) : (2:ℝ)^(2*i)*μ.real (amplitudeLevel f i)≤
      4*(∫ x in amplitudeLevel f i, ‖f x‖^2 ∂μ) := by
    have hp : (2:ℝ)^i=2*(2:ℝ)^(i-1) := by
      rw [show i=(i-1)+1 by omega,zpow_add₀ (by norm_num : (2:ℝ)≠0)]
      norm_num
      ring
    have hbound : (∫ _ in amplitudeLevel f i, ((2:ℝ)^i)^2/4 ∂μ)≤
        ∫ x in amplitudeLevel f i, ‖f x‖^2 ∂μ := by
      apply setIntegral_mono_on
        (integrableOn_const (amplitudeLevel_finite μ hf i)) hsq.integrableOn (amplitudeLevel_measurable hm i)
      intro x hx
      have hn : 0<(2:ℝ)^(i-1) := zpow_pos (by norm_num) _
      have hs := sq_le_sq₀ hn.le (norm_nonneg (f x)) |>.2 hx.1.le
      rw [hp]
      nlinarith only [hs]
    rw [setIntegral_const,smul_eq_mul] at hbound
    have he : (2:ℝ)^(2*i)=((2:ℝ)^i)^2 := by rw [mul_comm (2:ℤ) i,zpow_mul]; norm_num
    rw [he]
    nlinarith only [hbound]
  calc
    _ = ∑ i∈I, (2:ℝ)^(2*i)*μ.real (amplitudeLevel f i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow,Real.sq_sqrt measureReal_nonneg]
      congr 1
      rw [mul_comm (2:ℤ) i,zpow_mul]
      norm_num
    _ ≤ ∑ i∈I, 4*(∫ x in amplitudeLevel f i, ‖f x‖^2 ∂μ) := Finset.sum_le_sum (fun i _ => hlevel i)
    _ = 4*(∫ x in ⋃ i∈I, amplitudeLevel f i, ‖f x‖^2 ∂μ) := by
      rw [←Finset.mul_sum,integral_biUnion_finset I (fun i _ => amplitudeLevel_measurable hm i)
        (fun i _ j _ hij => amplitudeLevel_disjoint f hij) (fun _ _ => hsq.integrableOn)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (setIntegral_le_integral hsq
      (Filter.Eventually.of_forall (fun x => sq_nonneg ‖f x‖))) (by norm_num)

end LipschitzHilbert

end

end OAI
