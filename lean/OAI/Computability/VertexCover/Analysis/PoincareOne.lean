import Mathlib
import OAI.Computability.VertexCover.Fourier.Walsh
import OAI.Computability.VertexCover.PCP.UniformRestriction
import OAI.Computability.VertexCover.Fourier.SourceContexts

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Cube
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def intervalLaw : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • volume.restrict (Set.Icc (-1 : ℝ) 1)

instance : IsProbabilityMeasure intervalLaw := by
  constructor
  norm_num [intervalLaw, Measure.smul_apply, Real.volume_Icc]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem integral_intervalLaw (f : ℝ → ℝ) :
    ∫ x, f x ∂intervalLaw = (1/2 : ℝ) * ∫ x in Set.Icc (-1 : ℝ) 1, f x := by
  simp [intervalLaw, integral_smul_measure]

theorem intervalLaw_ac : intervalLaw ≪ volume := by
  intro s hs
  have hz : volume.restrict (Set.Icc (-1 : ℝ) 1) s = 0 :=
    le_antisymm ((Measure.restrict_le_self s).trans_eq hs) zero_le
  simp only [intervalLaw, Measure.smul_apply, hz, smul_zero]

noncomputable def law (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => intervalLaw)

instance law_probability (ι : Type*) [Fintype ι] : IsProbabilityMeasure (law ι) := by
  unfold law
  infer_instance

end VertexCover.Cube

namespace VertexCover.Cube
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem sq_integral_le_measure_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ)^2 ≤ μ.real Set.univ * ∫ x, (f x)^2 ∂μ := by
  have ha := norm_integral_le_integral_norm (μ := μ) f
  have hb := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
    (f := f) (g := fun _ => (1 : ℝ)) (by simpa using hf) (by simpa using memLp_const (1 : ℝ))
  simp only [Real.norm_eq_abs, abs_one, mul_one, Real.rpow_two, sq_abs,
    integral_const, smul_eq_mul, mul_one, one_pow] at hb
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hb
  have hz : 0 ≤ ∫ x, (f x)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hm : 0 ≤ μ.real Set.univ := ENNReal.toReal_nonneg
  have hc : |∫ x, f x ∂μ| ≤ Real.sqrt (∫ x, (f x)^2 ∂μ) * Real.sqrt (μ.real Set.univ) :=
    (show |∫ x, f x ∂μ| ≤ ∫ x, ‖f x‖ ∂μ from ha).trans hb
  have hd := sq_le_sq₀ (abs_nonneg (∫ x, f x ∂μ))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) |>.mpr hc
  simpa only [sq_abs, mul_pow, Real.sq_sqrt hz, Real.sq_sqrt hm, mul_comm] using hd

end VertexCover.Cube

namespace VertexCover.Cube
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem deriv_memLp {w : ℝ → ℝ} {C : NNReal} (hw : LipschitzWith C w)
    (a b : ℝ) : MemLp (deriv w) 2 (volume.restrict (Set.Icc a b)) := by
  exact MemLp.of_bound (measurable_deriv w).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun _ => norm_deriv_le_of_lipschitz hw))

theorem anchored_sq_le {w : ℝ → ℝ} {C : NNReal} (hw : LipschitzWith C w)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (w x - w 0)^2 ≤ ∫ y in Set.Icc (-1 : ℝ) 1, (deriv w y)^2 := by
  let a := min (0 : ℝ) x
  let b := max (0 : ℝ) x
  have hab : a ≤ b := (min_le_left _ _).trans (le_max_left _ _)
  have hlen : b - a ≤ 1 := by
    dsimp [a, b]
    rcases le_total 0 x with h | h
    · rw [min_eq_left h, max_eq_right h]; linarith [hx.2]
    · rw [min_eq_right h, max_eq_left h]; linarith [hx.1]
  have hsub : Set.Icc a b ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro y hy
    exact ⟨(le_min (by norm_num) hx.1).trans hy.1,
      hy.2.trans (max_le (by norm_num) hx.2)⟩
  have hftc := (hw.lipschitzOnWith (s := Set.uIcc (0 : ℝ) x)).absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have heq : (w x - w 0)^2 = (∫ y in Set.Icc a b, deriv w y)^2 := by
    rw [← hftc]
    rcases le_total 0 x with h | h
    · rw [intervalIntegral.integral_of_le h, ← integral_Icc_eq_integral_Ioc]
      simp [a, b, min_eq_left h, max_eq_right h]
    · rw [intervalIntegral.integral_of_ge h, ← integral_Icc_eq_integral_Ioc]
      simp [a, b, min_eq_right h, max_eq_left h]
  rw [heq]
  have hcs := sq_integral_le_measure_mul (volume.restrict (Set.Icc a b)) (deriv_memLp hw a b)
  have hm : (volume.restrict (Set.Icc a b)).real Set.univ = b - a := by
    simp [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [hm] at hcs
  have hnon : 0 ≤ ∫ y in Set.Icc a b, (deriv w y)^2 := integral_nonneg (fun _ => sq_nonneg _)
  refine hcs.trans ((mul_le_of_le_one_left hnon hlen).trans ?_)
  exact setIntegral_mono_set (deriv_memLp hw (-1) 1).integrable_sq
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall hsub)

theorem poincare_one {w : ℝ → ℝ} {C : NNReal} (hw : LipschitzWith C w) :
    variance w intervalLaw ≤ 2 * ∫ x, (deriv w x)^2 ∂intervalLaw := by
  have hm : AEStronglyMeasurable w intervalLaw := hw.continuous.measurable.aestronglyMeasurable
  have hs : AEStronglyMeasurable (fun x => w x - w 0) intervalLaw := hm.sub aestronglyMeasurable_const
  have hi : Integrable (fun x => (w x - w 0)^2) intervalLaw := by
    exact ((hw.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_Icc.smul_measure (by norm_num)
  have hbound : (fun x => (w x - w 0)^2) ≤ᵐ[intervalLaw]
      (fun _ => ∫ y in Set.Icc (-1 : ℝ) 1, (deriv w y)^2) := by
    have hae : ∀ᵐ x ∂intervalLaw, x ∈ Set.Icc (-1 : ℝ) 1 := by
      exact (Measure.ae_ennreal_smul_measure_iff (by norm_num : (1/2 : ℝ≥0∞) ≠ 0)).mpr
        (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hae] with x hx
    exact anchored_sq_le hw hx
  calc
    variance w intervalLaw = variance (fun x => w x - w 0) intervalLaw :=
      (variance_sub_const hm (w 0)).symm
    _ ≤ ∫ x, (w x - w 0)^2 ∂intervalLaw := variance_le_expectation_sq hs
    _ ≤ ∫ x, (∫ y in Set.Icc (-1 : ℝ) 1, (deriv w y)^2) ∂intervalLaw :=
      integral_mono_ae hi (integrable_const _) hbound
    _ = 2 * ∫ x, (deriv w x)^2 ∂intervalLaw := by
      rw [integral_const, integral_intervalLaw]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      ring

end VertexCover.Cube


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
