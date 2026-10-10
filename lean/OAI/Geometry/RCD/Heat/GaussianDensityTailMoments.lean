import OAI.Geometry.RCD.Heat.GaussianMomentIntegrable
import OAI.Geometry.RCD.Harmonic.IntegrableRadialTail

namespace OAI

/-! # One tail radius controls every integer density moment

The radius is independent of the member of the family and of the exponent.
-/

open Set Filter MeasureTheory Metric
noncomputable section
namespace RegularPointCoordinates
variable {X ι : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} {ρ : ι → X → ℝ}

theorem gaussian_density_tail_moments (p : X) {B L : ℝ} (hB : 0 < B)
    (hρm : ∀ i, Measurable (ρ i)) (hρ0 : ∀ i x, 0 ≤ ρ i x)
    (htail : ∀ i x, L ≤ dist x p → ρ i x ≤ B*Real.exp (-(dist x p)^2/40))
    (hG : Integrable (fun x => Real.exp (-(dist x p)^2/40)*(dist x p)^2) μ) :
    ∃ R : ℝ, 0 < R ∧ ∀ i (q : ℕ), 2 ≤ q →
      IntegrableOn (fun x => (ρ i x)^q*(dist x p)^2) (ball p R)ᶜ μ ∧
      (∫ x in (ball p R)ᶜ, (ρ i x)^q*(dist x p)^2 ∂μ) ≤ 1 := by
  obtain ⟨N,hN⟩ := ((integrable_radial_tail hG p).eventually
    (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num))).exists
  let R := max 1 (max L (max (Real.sqrt (80*max (Real.log B) 0)) (N:ℝ)))
  have hR1 : 1 ≤ R := le_max_left _ _
  have hRL : L ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRN : (N:ℝ) ≤ R := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hRs : Real.sqrt (80*max (Real.log B) 0) ≤ R := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hsub : (ball p R)ᶜ ⊆ (ball p (N:ℝ))ᶜ :=
    compl_subset_compl.mpr (ball_subset_ball hRN)
  have hGi := hG.integrableOn (s := (ball p R)ᶜ)
  refine ⟨R,lt_of_lt_of_le (by norm_num) hR1,?_⟩
  intro i q hq
  have hbound (x : X) (hx : x ∈ (ball p R)ᶜ) :
      (ρ i x)^q*(dist x p)^2 ≤ Real.exp (-(dist x p)^2/40)*(dist x p)^2 := by
    have hd : R ≤ dist x p := le_of_not_gt hx
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg (80*max (Real.log B) 0))
      (hRs.trans hd) 2
    rw [Real.sq_sqrt (by positivity)] at hs
    have hlog : Real.log B ≤ (dist x p)^2/80 := by
      have hh := le_max_left (Real.log B) 0
      linarith
    exact mul_le_mul_of_nonneg_right
      (gaussian_density_power_tail hB (hρ0 i x) (htail i x (hRL.trans hd)) hlog hq)
      (sq_nonneg _)
  have hi : IntegrableOn (fun x => (ρ i x)^q*(dist x p)^2) (ball p R)ᶜ μ := by
    apply hGi.mono'
    · exact ((hρm i).pow_const q |>.mul
        ((continuous_id.dist continuous_const).pow 2).measurable).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_ball.compl] with x hx
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg (hρ0 i x) q) (sq_nonneg _))]
      exact hbound x hx
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x in (ball p R)ᶜ, Real.exp (-(dist x p)^2/40)*(dist x p)^2 ∂μ :=
      setIntegral_mono_on hi hGi measurableSet_ball.compl hbound
    _ ≤ ∫ x in (ball p (N:ℝ))ᶜ, Real.exp (-(dist x p)^2/40)*(dist x p)^2 ∂μ :=
      setIntegral_mono_set hG.integrableOn (Eventually.of_forall (fun x => by positivity))
        (Eventually.of_forall (fun x hx => hsub hx))
    _ ≤ 1 := hN.le

end RegularPointCoordinates

end

end OAI
