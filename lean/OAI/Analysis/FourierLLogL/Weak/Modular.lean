import OAI.Analysis.FourierLLogL.Fourier.Endpoint
/-! # The Luxemburg gauge for the Fourier convergence class -/
noncomputable section
open MeasureTheory Filter Set Function
open scoped ENNReal BigOperators Topology

namespace OAI

namespace FourierLLogL

def priceΦ (x : ℝ) := x*Real.log (2+x)
def modBill (f : Torus → ℂ) (b : ℝ) := ∫ x, priceΦ (‖f x‖/b) ∂circleMeasure
def luxSet (f : Torus → ℂ) := {b | 0 < b ∧ modBill f b ≤ 1}
def luxNorm (f : Torus → ℂ) := sInf (luxSet f)

namespace Weak
open Real
open scoped Classical

lemma p_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ priceΦ x :=
    mul_nonneg hx (log_nonneg (by linarith))
lemma p_zero : priceΦ 0=0 := by simp [priceΦ]
lemma p_mono {x y : ℝ} (hx : 0 ≤ x) (he : x ≤ y) :
    priceΦ x ≤ priceΦ y := mul_le_mul he (log_le_log (by linarith) (by linarith))
      (log_nonneg (by linarith)) (hx.trans he)


private def slopeΦ (x : ℝ) := log (2+x)+x/(2+x)
private lemma p_support (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    priceΦ y+slopeΦ y*(x-y) ≤ priceΦ x := by
  let a := 2+x; let b := 2+y
  have ha : 0 < a := by unfold a; linarith
  have hb : 0 < b := by unfold b; linarith
  have H : (a-b)/a ≤ log a-log b := by
    have hi := log_le_sub_one_of_pos (div_pos hb ha)
    rw [log_div hb.ne' ha.ne'] at hi
    rw [sub_div,div_self ha.ne']; linarith
  have HH : y/b*(x-y) ≤ x*((a-b)/a) := by
    have HE : 0 ≤ 2*(x-y)^2/(a*b) := by positivity
    have HV : x*((a-b)/a)-y/b*(x-y)=2*(x-y)^2/(a*b) := by
      field_simp; unfold a b; ring
    linarith
  change y*log b + (log b + y/b)*(x-y) ≤ x*log a
  nlinarith

/-- Average of finitely many entries. -/
lemma price_convex {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℂ) :
    let a : ℝ := Fintype.card ι
    priceΦ ‖(a⁻¹:ℝ) • (∑ i, f i)‖ ≤ a⁻¹ * ∑ i,priceΦ ‖f i‖ := by
  intro a
  have ha : 0 < a := by unfold a; positivity
  let k := (∑ i, ‖f i‖)/a
  have hk : 0 ≤ k := by unfold k; positivity
  apply le_trans (b:=priceΦ k) (p_mono (norm_nonneg _) ?_)
  · rw [←div_eq_inv_mul]
    apply (le_div_iff₀ ha).mpr
    have HH : ∑ i : ι,(priceΦ k+slopeΦ k*(‖f i‖-k)) ≤ _ :=
      Finset.sum_le_sum fun (i : ι) (_ : i∈Finset.univ) => p_support ‖f i‖ k (norm_nonneg _) hk
    rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_sub_distrib] at HH
    simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ] at HH
    have H : ∑ i : ι,‖f i‖ = a*k := by unfold k; field_simp
    change a*priceΦ k+_ * (_-a*k) ≤ _ at HH
    rw [H] at HH; linarith
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr ha.le)]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr ha.le)).trans
  exact (div_eq_inv_mul _ _).ge

/-- Scalar comparison under every finite dilation. -/
lemma scale_admit (a : ℝ) (ha : 0 ≤ a) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x, 0 ≤ x → priceΦ (a*x) ≤ c*priceΦ x := by
  rcases le_total a 1 with h|h
  · refine ⟨1,by norm_num,fun x hx => ?_⟩; rw [one_mul]
    apply p_mono (mul_nonneg ha hx); nlinarith
  · refine ⟨a*(1+2*log a),by have := log_nonneg h; positivity,fun x hx => ?_⟩
    have HH : log (2+a*x) ≤ log a+log (2+x) := by
      rw [← log_mul (by positivity) (by positivity)]
      apply log_le_log (by positivity); nlinarith
    have hi : 1/2 ≤ log (2+x) :=
      le_trans (by linarith [Real.log_two_gt_d9]) (log_le_log (by norm_num : 0 < (2:ℝ)) (by linarith))
    have HR : log a ≤ 2*log a * log (2+x) := by nlinarith [log_nonneg h]
    unfold priceΦ; nlinarith [mul_le_mul_of_nonneg_left (le_trans HH (add_le_add_left HR _))
      (mul_nonneg ha hx)]

def Young (f : Torus → ℂ) (x : Torus) := priceΦ ‖f x‖
def inside (f : Torus → ℂ) := MemLLogL f ∧ modBill f 1 ≤ 1

lemma young_meas {f : Torus → ℂ} (h : AEStronglyMeasurable f circleMeasure) :
    AEStronglyMeasurable (Young f) circleMeasure := by
  have hp := h.norm
  unfold Young priceΦ
  exact hp.mul ((aemeasurable_const.add hp.aemeasurable).log).aestronglyMeasurable

lemma mem_dilate (c : ℂ) {f : Torus → ℂ} (hp : MemLLogL f) :
    MemLLogL (fun x => c*f x) := by
  let g (x : Torus) := c*f x
  have hi : AEStronglyMeasurable g circleMeasure := hp.1.const_mul _
  obtain ⟨v,hv,ht⟩ := scale_admit ‖c‖ (norm_nonneg _)
  refine ⟨hi,?_⟩
  change Integrable (Young g) circleMeasure
  apply ((show Integrable (Young f) _ from hp.2).const_mul v).mono' (young_meas hi)
  apply ae_of_all
  intro x
  change ‖Young g x‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ Young g x from p_nonneg _ (norm_nonneg _))]
  unfold Young g; rw [norm_mul]; apply ht; exact norm_nonneg _

lemma mod_unit (f : Torus → ℂ) :
    modBill f 1 = ∫ x, Young f x ∂circleMeasure := by simp only [modBill,div_one]; rfl

lemma sum_inside {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → Torus → ℂ) (h : ∀ i, inside (f i)) :
    let a : ℝ := Fintype.card ι
    inside (fun x => a⁻¹ • ∑ i, f i x) := by
  intro a
  let g (x : Torus) : ℂ := a⁻¹ • ∑ i, f i x
  let F (x : Torus) := a⁻¹ * ∑ i, Young (f i) x
  have ha : 0 < a := by unfold a; positivity
  have he (i) : Integrable (Young (f i)) circleMeasure := (h i).1.2
  have HH : AEStronglyMeasurable g circleMeasure := by
    unfold g
    have HH := Finset.aestronglyMeasurable_fun_sum Finset.univ (fun (i:ι) _ => (h i).1.1)
    exact HH.const_smul (a⁻¹)
  have HI : Integrable F circleMeasure := (integrable_finsetSum _ fun i _ => he i).const_mul _
  have HX (x : Torus) : Young g x ≤ F x := price_convex fun i => f i x
  have HV : Integrable (Young g) circleMeasure :=
    HI.mono' (young_meas HH) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ Young g x from p_nonneg _ (norm_nonneg _))]
      exact HX x)
  refine ⟨⟨HH,HV⟩,?_⟩
  rw [mod_unit]
  apply (integral_mono HV HI HX).trans
  unfold F; rw [integral_const_mul,integral_finsetSum _ (fun i _ => he i)]
  rw [←div_eq_inv_mul]
  apply (div_le_one ha).mpr
  have Hz (i) : ∫ x,Young (f i) x ∂circleMeasure ≤ 1 := by rw [←mod_unit]; exact (h i).2
  exact le_trans (Finset.sum_le_sum (fun i _ => Hz i)) (by simp [a])
end Weak
end FourierLLogL

end OAI
