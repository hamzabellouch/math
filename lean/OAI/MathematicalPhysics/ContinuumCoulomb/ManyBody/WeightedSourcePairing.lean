import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.H1PairingBound

namespace OAI

/-! Weighted Cauchy--Schwarz for the absolute nuclear error measure. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem weighted_real_pairing {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F f g : X → ℝ)
    (hF : AEMeasurable F μ) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hfi : Integrable (fun x => |F x| *f x^2) μ)
    (hgi : Integrable (fun x => |F x| *g x^2) μ) :
    Integrable (fun x => F x*f x*g x) μ ∧
      |∫ x, F x*f x*g x ∂μ|^2 ≤
        (∫ x, |F x| *f x^2 ∂μ)*(∫ x, |F x| *g x^2 ∂μ) := by
  let a : X → ℝ := fun x => Real.sqrt |F x| *|f x|
  let b : X → ℝ := fun x => Real.sqrt |F x| *|g x|
  have ha : AEMeasurable a μ := (Real.continuous_sqrt.measurable.comp_aemeasurable hF.abs).mul hf.abs
  have hb : AEMeasurable b μ := (Real.continuous_sqrt.measurable.comp_aemeasurable hF.abs).mul hg.abs
  have hasq (x : X) : a x^2 = |F x| *f x^2 := by
    dsimp [a]
    rw [mul_pow,Real.sq_sqrt (abs_nonneg _),sq_abs]
  have hbsq (x : X) : b x^2 = |F x| *g x^2 := by
    dsimp [b]
    rw [mul_pow,Real.sq_sqrt (abs_nonneg _),sq_abs]
  have hpa : MemLp a 2 μ := (memLp_two_iff_integrable_sq ha.aestronglyMeasurable).mpr (by simpa only [hasq] using hfi)
  have hpb : MemLp b 2 μ := (memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mpr (by simpa only [hbsq] using hgi)
  let A := hpa.toLp a
  let B := hpb.toLp b
  have hi : inner ℝ A B = ∫ x, a x*b x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hpa.coeFn_toLp,hpb.coeFn_toLp] with x hax hbx
    change inner ℝ (A x) (B x) = a x*b x
    rw [hax,hbx,Real.inner_apply]
  have hnA : ‖A‖^2 = ∫ x, |F x| *f x^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hpa.coeFn_toLp] with x hax
    rw [real_inner_self_eq_norm_sq,hax,Real.norm_eq_abs,sq_abs,hasq]
  have hnB : ‖B‖^2 = ∫ x, |F x| *g x^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hpb.coeFn_toLp] with x hbx
    rw [real_inner_self_eq_norm_sq,hbx,Real.norm_eq_abs,sq_abs,hbsq]
  have hab (x : X) : a x*b x = ‖F x*f x*g x‖ := by
    dsimp [a,b]
    rw [abs_mul,abs_mul]
    calc
      _ = (Real.sqrt |F x|)^2*(|f x| *|g x|) := by ring
      _ = _ := by rw [Real.sq_sqrt (abs_nonneg (F x))]; ring
  have hip := hpa.integrable_mul hpb
  have hIfg : Integrable (fun x => F x*f x*g x) μ := by
    apply hip.mono' ((hF.mul hf).mul hg).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => (hab x).ge)
  refine ⟨hIfg,?_⟩
  have hle : |∫ x, F x*f x*g x ∂μ| ≤ ∫ x, a x*b x ∂μ := by
    have h := norm_integral_le_integral_norm (μ := μ) (fun x => F x*f x*g x)
    simpa only [Real.norm_eq_abs,← hab] using h
  have hcs := pow_le_pow_left₀ (norm_nonneg (inner ℝ A B)) (norm_inner_le_norm (𝕜 := ℝ) A B) 2
  rw [mul_pow,hnA,hnB,hi,Real.norm_eq_abs,sq_abs] at hcs
  exact (pow_le_pow_left₀ (abs_nonneg _) hle 2).trans hcs

theorem weighted_source_pairing (F f g : Position → ℝ)
    (hF : Measurable F) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable (fun x => |F x| *f x^2))
    (hgi : Integrable (fun x => |F x| *g x^2)) :
    Integrable (fun x => F x*f x*g x) ∧
      |∫ x, F x*f x*g x|^2 ≤
        (∫ x, |F x| *f x^2)*(∫ x, |F x| *g x^2) :=
  weighted_real_pairing volume F f g hF.aemeasurable hf.aemeasurable hg.aemeasurable hfi hgi

end ContinuumCoulomb

end

end OAI
