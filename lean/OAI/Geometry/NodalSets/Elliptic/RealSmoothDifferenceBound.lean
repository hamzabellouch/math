import Mathlib.MeasureTheory.Integral.Prod
import OAI.Geometry.NodalSets.Elliptic.RealDifferenceQuotientTest
import OAI.Geometry.NodalSets.Elliptic.RealIntervalDerivativeControl

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_line_coord_deriv {n : ℕ} (u : Coord n → ℝ) (hu : ContDiff ℝ ∞ u)
    (i : Fin n) (h t : ℝ) (x : Coord n) :
    deriv (fun s : ℝ ↦ u (x+s • (Pi.single i h : Coord n))) t =
      h*coordPartial u (x+t • (Pi.single i h : Coord n)) i := by
  have hd := (hu.differentiable (by simp) (x+t • (Pi.single i h : Coord n))).hasFDerivAt
  have hp : HasDerivAt (fun s : ℝ ↦ x+s • (Pi.single i h : Coord n)) (Pi.single i h) t := by
    simpa using ((hasDerivAt_id t).smul_const (Pi.single i h : Coord n)).const_add x
  have hh : (Pi.single i h : Coord n)=h • (Pi.single i 1 : Coord n) := by
    ext j
    by_cases hj : j=i <;> simp [hj]
  have hd' := (hd.comp_hasDerivAt t hp).deriv
  simp only [Function.comp_def] at hd'
  rw [hd']
  simp only [coordPartial,hh,map_smul,smul_eq_mul]

theorem realDifferenceQuotient_sq_pointwise {n : ℕ} (u : Coord n → ℝ)
    (hu : ContDiff ℝ ∞ u) (i : Fin n) (h : ℝ) (x : Coord n) :
    (realDifferenceQuotient i h u x)^2 ≤
      ∫ t in Icc (0:ℝ) 1, (coordPartial u (x+t • (Pi.single i h : Coord n)) i)^2 := by
  by_cases hh : h=0
  · subst h
    simp only [realDifferenceQuotient,inv_zero,zero_mul,zero_pow (by decide : 2≠0)]
    exact integral_nonneg (fun _ ↦ sq_nonneg _)
  have hs : ContDiff ℝ ∞ (fun t : ℝ ↦ u (x+t • (Pi.single i h : Coord n))) :=
    hu.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hb := Yau.Geometry.real_interval_derivative_control _ hs
    (by norm_num : (0:ℝ)<1) 1 0 (by norm_num) (by norm_num)
  simp only [one_smul,zero_smul,add_zero,sub_zero,one_mul,real_line_coord_deriv u hu,
    mul_pow] at hb
  rw [integral_const_mul] at hb
  have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg h⁻¹)
  calc
    _ = h⁻¹^2*(u (x+Pi.single i h)-u x)^2 := mul_pow _ _ _
    _ ≤ h⁻¹^2*(h^2*(∫ t in Icc (0:ℝ) 1, (coordPartial u (x+t • (Pi.single i h : Coord n)) i)^2)) := hb'
    _ = _ := by field_simp

theorem real_translation_square_integrable {n : ℕ} (g : Coord n → ℝ)
    (hg : Continuous g) (hm : MemLp g 2 volume) (v : Coord n) :
    Integrable (fun q : Coord n × ℝ ↦ (g (q.1+q.2 • v))^2)
      (volume.prod (volume.restrict (Icc (0:ℝ) 1))) := by
  have hc : Continuous (fun q : Coord n × ℝ ↦ (g (q.1+q.2 • v))^2) :=
    (hg.comp (continuous_fst.add (continuous_snd.smul continuous_const))).pow 2
  apply (integrable_prod_iff' hc.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun t ↦ (hm.comp_measurePreserving
      (measurePreserving_add_right volume (t • v))).integrable_sq)
  · have he : (fun t : ℝ ↦ ∫ x : Coord n, ‖(g (x+t • v))^2‖) =
        fun _ : ℝ ↦ ∫ x : Coord n, (g x)^2 := by
      funext t
      simp only [Real.norm_eq_abs,abs_sq]
      exact integral_add_right_eq_self (fun x ↦ (g x)^2) (t • v)
    rw [he]
    exact integrable_const _

theorem real_smooth_difference_bound {n : ℕ} (u : Coord n → ℝ)
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (i : Fin n) (h : ℝ) :
    MemLp (realDifferenceQuotient i h u) 2 volume ∧
      (∫ x, (realDifferenceQuotient i h u x)^2) ≤ ∫ x, (coordPartial u x i)^2 := by
  have hd := real_coordPartial_smooth u hu i
  have hm := real_compact_continuous_memLp _ hd.continuous (hc.fderiv_apply ℝ (Pi.single i 1))
  have hq := realDifferenceQuotient_memLp i h u (real_compact_continuous_memLp u hu.continuous hc)
  have hp := real_translation_square_integrable _ hd.continuous hm (Pi.single i h)
  refine ⟨hq,?_⟩
  calc
    _ ≤ ∫ x, ∫ t in Icc (0:ℝ) 1, (coordPartial u (x+t • (Pi.single i h : Coord n)) i)^2 :=
      integral_mono hq.integrable_sq hp.integral_prod_left (realDifferenceQuotient_sq_pointwise u hu i h)
    _ = ∫ t in Icc (0:ℝ) 1, ∫ x, (coordPartial u (x+t • (Pi.single i h : Coord n)) i)^2 :=
      integral_integral_swap hp
    _ = _ := by
      simp_rw [integral_add_right_eq_self (fun x ↦ (coordPartial u x i)^2)]
      simp

end
end Yau

end OAI
