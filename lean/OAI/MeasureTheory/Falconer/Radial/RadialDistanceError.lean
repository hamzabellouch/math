import OAI.MeasureTheory.Falconer.Shells.RadialShellMass
import OAI.MeasureTheory.Falconer.Estimates.InactivePairMass
import OAI.MeasureTheory.Falconer.Estimates.DistanceForm

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def sourceRadialSquareEnergy (a v : ℝ) (Ψ : ℝ → ℝ) (F : ℝ → ℂ) : ℝ :=
  (2:ℝ)^(2*(v-a)) * ∫ r, ‖F r‖^2 ∂sourceAngularShellMeasure v Ψ

theorem integrable_norm_square_bounded (μ : Measure ℝ) [IsFiniteMeasure μ]
    (F : ℝ → ℂ) (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ r ∂μ, ‖F r‖ ≤ B) : Integrable (fun r => ‖F r‖^2) μ := by
  apply (integrable_const (B^2)).mono (hF.norm.pow_const 2).aestronglyMeasurable
  filter_upwards [hb] with r hr
  simp only [norm_pow, Real.norm_eq_abs, abs_of_nonneg hB, abs_of_nonneg (norm_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hr 2

theorem sourceDistanceHF_eq_ofReal (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (sourceAngularShellMeasure v Ψ)]
    (ψ : UnitCircle → ℂ) (U V : ℝ × UnitCircle → ℂ)
    (hF : Measurable (sourceDistanceF ψ U V)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ r ∂sourceAngularShellMeasure v Ψ, ‖sourceDistanceF ψ U V r‖ ≤ B) :
    sourceDistanceHF a v Ψ ψ U V =
      ENNReal.ofReal (sourceRadialSquareEnergy a v Ψ (sourceDistanceF ψ U V)) := by
  have hi := integrable_norm_square_bounded (sourceAngularShellMeasure v Ψ) _ hF hB hb
  have he : (∫⁻ r, ‖sourceDistanceF ψ U V r‖ₑ^2 ∂sourceAngularShellMeasure v Ψ) =
      ENNReal.ofReal (∫ r, ‖sourceDistanceF ψ U V r‖^2 ∂sourceAngularShellMeasure v Ψ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun r => sq_nonneg _))]
    apply lintegral_congr
    intro r
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [sourceDistanceHF, he, ← ENNReal.ofReal_mul (by positivity)]
  rfl

theorem sourceRadialSquareEnergy_error_le (a v : ℝ) (Ψ : ℝ → ℝ)
    {W : ℝ} (hW : 0 ≤ W) (hΨ : ∀ t, Ψ t ≤ W) (hs : ∀ t, 4 < t → Ψ t = 0)
    (F G : ℝ → ℂ) (hF : Measurable F) (hG : Measurable G)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hGb : ∀ᵐ r ∂sourceAngularShellMeasure v Ψ, ‖G r‖ ≤ B)
    (he : ∀ᵐ r ∂sourceAngularShellMeasure v Ψ, ‖F r-G r‖ ≤ ε) :
    |sourceRadialSquareEnergy a v Ψ F - sourceRadialSquareEnergy a v Ψ G| ≤
      (2:ℝ)^(2*(v-a)) * (2*B*ε+ε^2) * (4*W) := by
  let μ := sourceAngularShellMeasure v Ψ
  let : IsFiniteMeasure μ := sourceAngularShellMeasure_finite v Ψ hW hΨ hs
  have hFb : ∀ᵐ r ∂μ, ‖F r‖ ≤ B+ε := by
    filter_upwards [hGb, he] with r hgr her
    have ht := norm_add_le (G r) (F r-G r)
    rw [add_sub_cancel] at ht
    exact ht.trans (add_le_add hgr her)
  have hFi := integrable_norm_square_bounded μ F hF (add_nonneg hB hε) hFb
  have hGi := integrable_norm_square_bounded μ G hG hB hGb
  have herr : ∀ᵐ r ∂μ, ‖‖F r‖^2-‖G r‖^2‖ ≤ 2*B*ε+ε^2 := by
    filter_upwards [hGb, he] with r hgr her
    have hh := complex_squared_norm_error (G r) (F r-G r)
    rw [add_sub_cancel] at hh
    apply hh.trans
    gcongr
  have hi := norm_integral_le_of_norm_le_const herr
  have hmass := sourceAngularShellMeasure_real_mass_le v Ψ hW hΨ hs
  unfold sourceRadialSquareEnergy
  rw [← mul_sub, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _),
    ← integral_sub hFi hGi]
  apply (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (2:ℝ)^(2*(v-a)))).trans
  calc
    _ = (2:ℝ)^(2*(v-a)) * (2*B*ε+ε^2) * μ.real univ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

end PlanarFalconer

end OAI
