import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

namespace OAI

/-!
# Vanishing of expanding scalar coordinates in a finite invariant law

This is the scalar step in diagonal recurrence on projective or
Grassmannian coordinates. Bounded monotone truncation avoids assuming
that the original coordinate is integrable. It will be applied to ratios
of unequal diagonal weights; no stabilizer or orbit conclusion is assumed.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace DukePrimeDegree

def boundedAbsCoordinate (x : ℝ) : ℝ := |x| / (1 + |x|)

lemma boundedAbsCoordinate_nonneg (x : ℝ) : 0 ≤ boundedAbsCoordinate x :=
  div_nonneg (abs_nonneg x) (by positivity)

lemma boundedAbsCoordinate_le_one (x : ℝ) : boundedAbsCoordinate x ≤ 1 := by
  apply (div_le_iff₀ (by positivity : 0 < 1 + |x|)).mpr
  nlinarith [abs_nonneg x]

lemma boundedAbsCoordinate_mono {x y : ℝ} (h : |x| ≤ |y|) :
    boundedAbsCoordinate x ≤ boundedAbsCoordinate y := by
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + |x|)
    (by positivity : 0 < 1 + |y|)).mpr
  nlinarith

lemma boundedAbsCoordinate_strictMono {x y : ℝ} (h : |x| < |y|) :
    boundedAbsCoordinate x < boundedAbsCoordinate y := by
  apply (div_lt_div_iff₀ (by positivity : 0 < 1 + |x|)
    (by positivity : 0 < 1 + |y|)).mpr
  nlinarith

/-- An a.e. expanding scalar coordinate must vanish under a finite
invariant measure. The scalar coordinate itself need not be integrable. -/
theorem ae_eq_zero_of_expanding_covariance
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (f : Y → ℝ) (hf : Measurable f) (c : ℝ) (hc : 1 < c)
    (hcov : (fun x => f (T x)) =ᵐ[μ] fun x => c * f x) :
    f =ᵐ[μ] 0 := by
  let g : Y → ℝ := fun x => boundedAbsCoordinate (f x)
  have hc0 : 0 < c := zero_lt_one.trans hc
  have habs : Measurable (fun x => |f x|) := continuous_abs.measurable.comp hf
  have hgm : Measurable g := habs.div (measurable_const.add habs)
  have hglp : MemLp g 1 μ :=
    MemLp.of_bound hgm.aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (boundedAbsCoordinate_nonneg _)]
      exact boundedAbsCoordinate_le_one _)
  have hgi : Integrable g μ := memLp_one_iff_integrable.mp hglp
  have hle : g ≤ᵐ[μ] fun x => g (T x) := by
    filter_upwards [hcov] with x hx
    change boundedAbsCoordinate (f x) ≤ boundedAbsCoordinate (f (T x))
    rw [hx]
    apply boundedAbsCoordinate_mono
    rw [abs_mul, abs_of_pos hc0]
    nlinarith [abs_nonneg (f x)]
  have hi : (∫ x, g (T x) ∂μ) = ∫ x, g x ∂μ := by
    have he := integral_map hT.measurable.aemeasurable
      (show AEStronglyMeasurable g (μ.map T) from by
        rw [hT.map_eq]
        exact hgm.aestronglyMeasurable)
    rw [hT.map_eq] at he
    exact he.symm
  have hgTi : Integrable (fun x => g (T x)) μ :=
    memLp_one_iff_integrable.mp (hglp.comp_measurePreserving hT)
  have he := (integral_eq_iff_of_ae_le hgi hgTi hle).mp hi.symm
  filter_upwards [he, hcov] with x hx hxcov
  change f x = 0
  by_contra hne
  have hlt : boundedAbsCoordinate (f x) < boundedAbsCoordinate (f (T x)) := by
    rw [hxcov]
    apply boundedAbsCoordinate_strictMono
    rw [abs_mul, abs_of_pos hc0]
    nlinarith [abs_pos.mpr hne]
  exact (ne_of_lt hlt) hx

end DukePrimeDegree

end

end OAI
