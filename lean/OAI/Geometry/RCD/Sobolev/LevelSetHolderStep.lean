import OAI.Geometry.RCD.Sobolev.LocalHolderMoment
import OAI.Geometry.RCD.Sobolev.SobolevLevelChain

namespace OAI

/-! # The level-set recurrence from a cutoff moment estimate -/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

private theorem upper_level_square_integrable (u : Lp ℝ 2 μ) {k : ℝ} (hk : 0 ≤ k) :
    Integrable (fun x => (max (u x-k) 0)^2) μ := by
  exact ((upperLevelPart_lipschitz k).comp_memLp (upperLevelPart_zero hk)
    (Lp.memLp u)).integrable_sq

/-- A higher moment on the outer domain, together with agreement of the
cutoff on the inner domain, gives the superlinear level-set estimate. -/
theorem level_set_holder_step {Ω B D : Set X} (hΩ : MeasurableSet Ω)
    (hB : MeasurableSet B) (hBΩ : B ⊆ Ω) (hBD : B ⊆ D) (hfin : μ Ω < ∞)
    (u z : Lp ℝ 2 μ) {k h p : ℝ} (hk : 0 ≤ k) (hkh : k < h) (hp : 2 < p)
    (hrep : z =ᵐ[μ.restrict B] fun x => max (u x-k) 0)
    (hi : IntegrableOn (fun x => |z x|^p) Ω μ) :
    (∫ x in B, (max (u x-h) 0)^2 ∂μ) ≤
      (∫ x in Ω, |z x|^p ∂μ)^(2/p)*
        ((∫ x in D, (max (u x-k) 0)^2 ∂μ)/(h-k)^2)^(1-2/p) := by
  classical
  let A := B ∩ {x | h < u x}
  have hA : MeasurableSet A := hB.inter
    (measurableSet_lt measurable_const (Lp.stronglyMeasurable u).measurable)
  have hAB : A ⊆ B := inter_subset_left
  have hAΩ : A ⊆ Ω := hAB.trans hBΩ
  have hAf : μ A ≠ ∞ := (lt_of_le_of_lt (measure_mono hAΩ) hfin).ne
  let : IsFiniteMeasure (μ.restrict A) := ⟨by simpa using hAf.lt_top⟩
  have hki := upper_level_square_integrable μ u hk
  have hhi := upper_level_square_integrable μ u (hk.trans hkh.le)
  have hrep' : ∀ᵐ x ∂μ, x ∈ B → z x = max (u x-k) 0 := (ae_restrict_iff' hB).mp hrep
  have hsmall : (∫ x in B, (max (u x-h) 0)^2 ∂μ) ≤ ∫ x in A, (z x)^2 ∂μ := by
    rw [← integral_indicator hB,← integral_indicator hA]
    apply integral_mono_ae (hhi.indicator hB) ((Lp.memLp z).integrable_sq.indicator hA)
    filter_upwards [hrep'] with x hx
    by_cases hxB : x ∈ B
    · by_cases hxu : h < u x
      · have hxA : x ∈ A := ⟨hxB,hxu⟩
        rw [indicator_of_mem hxB,indicator_of_mem hxA,hx hxB,
          max_eq_left (by linarith : 0 ≤ u x-h),max_eq_left (by linarith : 0 ≤ u x-k)]
        nlinarith
      · have hxA : x ∉ A := fun hh => hxu hh.2
        rw [indicator_of_mem hxB,indicator_of_notMem hxA,
          max_eq_right (by linarith : u x-h ≤ 0),zero_pow (by decide)]
    · rw [indicator_of_notMem hxB,indicator_of_notMem (fun hh => hxB hh.1)]
  have hmeasure : μ.real A ≤ (∫ x in D, (max (u x-k) 0)^2 ∂μ)/(h-k)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hkh))).mpr
    calc
      μ.real A*(h-k)^2 = ∫ _x in A, (h-k)^2 ∂μ := by simp only [integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply_univ]
      _ ≤ ∫ x in A, (max (u x-k) 0)^2 ∂μ := by
        apply integral_mono_ae (integrable_const _) hki.integrableOn
        filter_upwards [ae_restrict_mem hA] with x hx
        have hxu : h < u x := hx.2
        rw [max_eq_left (by linarith : 0 ≤ u x-k)]
        nlinarith [sq_nonneg (u x-h)]
      _ ≤ _ := setIntegral_mono_set hki.integrableOn
        (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall (hAB.trans hBD))
  have hholder := square_setIntegral_le_higher_moment μ hΩ hA hAΩ hfin
    (Lp.aestronglyMeasurable z).restrict hp hi
  have hp0 : 0 < p := by linarith
  have hα : 0 ≤ 1-2/p := by
    have hh : 2/p < 1 := (div_lt_one hp0).mpr hp
    linarith
  exact hsmall.trans (hholder.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (measureReal_nonneg) hmeasure hα) (by positivity)))

end RegularPointCoordinates

end

end OAI
