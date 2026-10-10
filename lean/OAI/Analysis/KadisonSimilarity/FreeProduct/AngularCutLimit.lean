import OAI.Analysis.KadisonSimilarity.FreeProduct.SpectralArcResolvents
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Bounded convergence of the angular cut functions and the elementary
identification of the limiting open angular arc. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter Set
open scoped Topology

theorem angularIntegral_cut_tendsto (c : ℝ) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) (l : ℤ) :
    Tendsto (fun n => angularIntegral
      (fun x => (spectralCutFunction c (ε n) (Real.cos x) : ℂ)) l) atTop
      (𝓝 (angularIntegral (fun x => if c < Real.cos x then 1 else 0) l)) := by
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have ht : Tendsto (fun n => ∫ x in -Real.pi..Real.pi,
        (spectralCutFunction c (ε n) (Real.cos x) : ℂ) * angularCharacter l x) atTop
      (𝓝 (∫ x in -Real.pi..Real.pi,
        (if c < Real.cos x then 1 else 0) * angularCharacter l x)) := by
    simp only [intervalIntegral.integral_of_le hπ]
    apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1 : ℝ))
    · intro n
      exact ((Complex.continuous_ofReal.comp
        ((spectralCutFunction_continuous c (hε n)).comp Real.continuous_cos)).mul
        (angularCharacter_continuous l)).aestronglyMeasurable
    · change IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (-Real.pi) Real.pi) volume
      simpa only [uIoc_of_le hπ] using
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ))
          volume (-Real.pi) Real.pi).1
    · intro n
      filter_upwards [] with x
      rw [norm_mul, norm_angularCharacter, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (spectralCutFunction_nonneg c _ (hε n))]
      exact spectralCutFunction_le_one c _ (hε n)
    · filter_upwards [] with x
      have h := (Complex.continuous_ofReal.tendsto _).comp
        (spectralCutFunction_tendsto c (Real.cos x) ε hε hlim)
      by_cases hc : c < Real.cos x <;>
        simpa only [Function.comp_apply, hc, ite_true, ite_false,
          Complex.ofReal_one, Complex.ofReal_zero] using h.mul_const (angularCharacter l x)
  exact ht.const_smul ((2 * Real.pi)⁻¹ : ℝ)

theorem cos_gt_iff_mem_open_arc {θ x : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hx : x ∈ Icc (-Real.pi) Real.pi) :
    Real.cos θ < Real.cos x ↔ x ∈ Ioo (-θ) θ := by
  have hxπ : |x| ≤ Real.pi := abs_le.mpr hx
  have h := Real.strictAntiOn_cos.lt_iff_gt ⟨hθ, hθπ⟩ ⟨abs_nonneg x, hxπ⟩
  rw [Real.cos_abs] at h
  simpa only [mem_Ioo, abs_lt] using h

theorem angularIntegral_centered_cut {θ : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (l : ℤ) :
    angularIntegral (fun x => (if Real.cos θ < Real.cos x then 1 else 0) -
      (θ / Real.pi : ℂ)) l = arcFourierIntegral θ l := by
  unfold angularIntegral arcFourierIntegral
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    (volume.restrict (uIoc (-Real.pi) Real.pi)).ae_ne θ] with x hx hne
  rw [uIoc_of_le (by linarith [Real.pi_pos])] at hx
  have hcos := cos_gt_iff_mem_open_arc hθ hθπ (show x ∈ Icc (-Real.pi) Real.pi from ⟨hx.1.le, hx.2⟩)
  have hm : Real.cos θ < Real.cos x ↔ x ∈ Ioc (-θ) θ := by
    rw [hcos]
    exact and_congr_right fun _ => ⟨fun h => h.le, fun h => lt_of_le_of_ne h hne⟩
  by_cases hi : x ∈ Ioc (-θ) θ
  · simp only [hm.mpr hi, ite_true, centeredArc, indicator_of_mem hi, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_div, angularCharacter]
  · simp only [not_congr hm |>.mpr hi, ite_false, centeredArc, indicator_of_notMem hi,
      Complex.ofReal_sub, Complex.ofReal_zero, Complex.ofReal_div, angularCharacter]

theorem angularIntegral_cut_eq {θ : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) (l : ℤ) :
    angularIntegral (fun x => if Real.cos θ < Real.cos x then 1 else 0) l =
      arcFourierIntegral θ l + (θ / Real.pi : ℂ) * angularPowerMoment 0 l := by
  let S : Set ℝ := {x | Real.cos θ < Real.cos x}
  have hS : MeasurableSet S := (isOpen_lt continuous_const Real.continuous_cos).measurableSet
  have hc : IntervalIntegrable (angularCharacter l) volume (-Real.pi) Real.pi :=
    (angularCharacter_continuous l).intervalIntegrable _ _
  have hcut : IntervalIntegrable
      (fun x => (if Real.cos θ < Real.cos x then 1 else 0) * angularCharacter l x)
      volume (-Real.pi) Real.pi := by
    have hi : IntervalIntegrable (S.indicator (angularCharacter l)) volume (-Real.pi) Real.pi :=
      ⟨hc.1.indicator hS, hc.2.indicator hS⟩
    convert hi using 1
    funext x
    by_cases hx : Real.cos θ < Real.cos x <;> simp [S, indicator, hx]
  have hconst : IntervalIntegrable
      (fun x => (θ / Real.pi : ℂ) * angularCharacter l x) volume (-Real.pi) Real.pi :=
    hc.const_mul _
  have h := angularIntegral_sub (fun x => if Real.cos θ < Real.cos x then 1 else 0)
    (fun _ => (θ / Real.pi : ℂ)) l hcut hconst
  rw [angularIntegral_centered_cut hθ hθπ l, angularIntegral_const] at h
  exact (sub_eq_iff_eq_add).mp h.symm

end KadisonSimilarity

end

end OAI
