import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! Bounded real weights on the two radial L² measures used by the harmonic form. -/

open MeasureTheory
namespace DefocusingNLS

private theorem spectralL2Multiplier_memLp (μ : Measure ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q μ) (M : ℝ) (hb : ∀ᵐ r ∂μ, ‖q r‖ ≤ M) (u : Lp ℂ 2 μ) :
    MemLp (fun r => q r • u r) 2 μ := by
  apply (Lp.memLp u).of_le_mul (hq.smul (Lp.aestronglyMeasurable u))
  filter_upwards [hb] with r hr
  change ‖q r • u r‖ ≤ M*‖u r‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hr (norm_nonneg _)

noncomputable def spectralL2Weight (μ : Measure ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q μ) (M : ℝ) (hb : ∀ᵐ r ∂μ, ‖q r‖ ≤ M)
    (u : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (spectralL2Multiplier_memLp μ q hq M hb u).toLp (fun r => q r • u r)

theorem spectralL2Weight_ae (μ : Measure ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q μ) (M : ℝ) (hb : ∀ᵐ r ∂μ, ‖q r‖ ≤ M) (u : Lp ℂ 2 μ) :
    spectralL2Weight μ q hq M hb u =ᵐ[μ] (fun r => q r • u r) := MemLp.coeFn_toLp _

theorem spectralL2Weight_norm (μ : Measure ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q μ) (M : ℝ) (hb : ∀ᵐ r ∂μ, ‖q r‖ ≤ M) (u : Lp ℂ 2 μ) :
    ‖spectralL2Weight μ q hq M hb u‖ ≤ M*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [spectralL2Weight_ae μ q hq M hb u,hb] with r he hr
  rw [he,norm_smul]
  exact mul_le_mul_of_nonneg_right hr (norm_nonneg _)

noncomputable def spectralL2Multiplier (μ : Measure ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q μ) (M : ℝ) (hb : ∀ᵐ r ∂μ, ‖q r‖ ≤ M) :
    Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ :=
  let A := spectralL2Weight μ q hq M hb
  let L : Lp ℂ 2 μ →ₗ[ℝ] Lp ℂ 2 μ :=
    { toFun := A
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [spectralL2Weight_ae μ q hq M hb (u+v),
          spectralL2Weight_ae μ q hq M hb u,spectralL2Weight_ae μ q hq M hb v,
          Lp.coeFn_add u v,Lp.coeFn_add (A u) (A v)] with r hsum hu hv hin hout
        change A (u+v) r=(A u+A v : Lp ℂ 2 μ) r
        rw [hsum,hout,hin,Pi.add_apply,Pi.add_apply,hu,hv,smul_add]
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [spectralL2Weight_ae μ q hq M hb (c • u),
          spectralL2Weight_ae μ q hq M hb u,Lp.coeFn_smul c u,
          Lp.coeFn_smul c (A u)] with r hcu hu hin hout
        change A (c • u) r=(c • A u : Lp ℂ 2 μ) r
        rw [hcu,hout,hin,Pi.smul_apply,Pi.smul_apply,hu]
        exact smul_comm (q r) c (u r) }
  L.mkContinuous M (fun u => by
    change ‖spectralL2Weight μ q hq M hb u‖ ≤ M*‖u‖
    exact spectralL2Weight_norm μ q hq M hb u)

theorem spectralL2Multiplier_quadratic (μ : Measure ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q μ) (M : ℝ) (hb : ∀ᵐ r ∂μ, ‖q r‖ ≤ M) (u : Lp ℂ 2 μ) :
    inner ℝ (spectralL2Multiplier μ q hq M hb u) u=∫ r, q r*‖u r‖^2 ∂μ := by
  change (∫ r, inner ℝ (spectralL2Weight μ q hq M hb u r) (u r) ∂μ)=_
  apply integral_congr_ae
  filter_upwards [spectralL2Weight_ae μ q hq M hb u] with r hr
  rw [hr,real_inner_smul_left,real_inner_self_eq_norm_sq]

theorem spectralL2Multiplier_lower (μ : Measure ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q μ) (M : ℝ) (hb : ∀ᵐ r ∂μ, ‖q r‖ ≤ M)
    (c : ℝ) (hc : ∀ᵐ r ∂μ, c ≤ q r) (u : Lp ℂ 2 μ) :
    c*‖u‖^2 ≤ inner ℝ (spectralL2Multiplier μ q hq M hb u) u := by
  have he : 0 ≤ inner ℝ (spectralL2Multiplier μ q hq M hb u-c • u) u := by
    change 0 ≤ ∫ r, inner ℝ ((spectralL2Multiplier μ q hq M hb u-c • u : Lp ℂ 2 μ) r) (u r) ∂μ
    apply integral_nonneg_of_ae
    filter_upwards [spectralL2Weight_ae μ q hq M hb u,
      Lp.coeFn_sub (spectralL2Multiplier μ q hq M hb u) (c • u),Lp.coeFn_smul c u,hc]
      with r hqv hsub hsmul hlow
    change spectralL2Multiplier μ q hq M hb u r=q r • u r at hqv
    rw [hsub,Pi.sub_apply,hqv,hsmul,Pi.smul_apply,inner_sub_left,
      real_inner_smul_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
    simp only [Pi.zero_apply]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlow) (sq_nonneg ‖u r‖)]
  rw [inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq] at he
  linarith

end DefocusingNLS

end OAI
