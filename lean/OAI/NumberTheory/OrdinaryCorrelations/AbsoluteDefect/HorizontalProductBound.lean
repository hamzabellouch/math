import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.NormCauchy

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set

namespace OrdinaryCompactCauchy
open MeasureTheory Set

theorem horizontal_product_bound {F₀ G₀ P : ℝ → ℂ} {G : ℝ × ℝ → ℂ}
    {M E : ℝ → ℝ} {l r a b B E₀ EP : ℝ}
    (hP : ContinuousOn P (Icc l r))
    (hF : ContinuousOn F₀ (Icc l r)) (hG₀ : ContinuousOn G₀ (Icc l r))
    (hG : ContinuousOn G (Icc a b ×ˢ Icc l r))
    (hM : ContinuousOn M (Icc a b)) (hE : ContinuousOn E (Icc a b))
    (hM0 : ∀x∈Icc a b, 0≤M x) (hB : 0≤B)
    (hEP : (∫t in Icc l r, ‖P t‖^2)≤EP)
    (hE₀ : (∫t in Icc l r, ‖G₀ t‖^2)≤E₀)
    (henergy : ∀x∈Icc a b, (∫t in Icc l r, ‖G (x,t)‖^2)≤E x)
    (hdecomp : ∀t∈Icc l r, ‖F₀ t‖ ≤ B*‖P t‖ + ∫x in Icc a b, M x*‖G (x,t)‖) :
    (∫t in Icc l r, ‖F₀ t‖*‖G₀ t‖) ≤
      B*Real.sqrt EP*Real.sqrt E₀ +
        Real.sqrt E₀*(∫x in Icc a b, M x*Real.sqrt (E x)) := by
  let H : ℝ × ℝ → ℝ := fun p => M p.1*‖G₀ p.2‖*‖G p‖
  have hMc : ContinuousOn (fun p : ℝ×ℝ => M p.1) (Icc a b ×ˢ Icc l r) :=
    hM.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hGc : ContinuousOn (fun p : ℝ×ℝ => G₀ p.2) (Icc a b ×ˢ Icc l r) :=
    hG₀.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hH : ContinuousOn H (Icc a b ×ˢ Icc l r) := (hMc.mul hGc.norm).mul hG.norm
  have hiH := rectangle_integrable hH
  have hbase : IntegrableOn (fun t => B*(‖P t‖*‖G₀ t‖)) (Icc l r) := by
    exact (continuousOn_const.mul (hP.norm.mul hG₀.norm)).integrableOn_Icc
  have hright : IntegrableOn (fun t => B*(‖P t‖*‖G₀ t‖) + ∫x in Icc a b, H (x,t)) (Icc l r) :=
    hbase.add hiH.integral_prod_right
  have hle : (∫t in Icc l r, ‖F₀ t‖*‖G₀ t‖) ≤
      ∫t in Icc l r, B*(‖P t‖*‖G₀ t‖) + ∫x in Icc a b, H (x,t) := by
    apply integral_mono_ae (hF.norm.mul hG₀.norm).integrableOn_Icc hright
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hh := mul_le_mul_of_nonneg_right (hdecomp t ht) (norm_nonneg (G₀ t))
    refine hh.trans_eq ?_
    rw [add_mul,mul_assoc]
    congr 1
    rw [←MeasureTheory.integral_mul_const]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    dsimp [H]
    ring
  have hout : (∫x in Icc a b, ∫t in Icc l r, H (x,t)) ≤
      Real.sqrt E₀*(∫x in Icc a b, M x*Real.sqrt (E x)) := by
    rw [←MeasureTheory.integral_const_mul]
    apply integral_mono_ae hiH.integral_prod_left
      ((hM.mul hE.sqrt).integrableOn_Icc.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hgx : ContinuousOn (fun t => G (x,t)) (Icc l r) :=
      hG.comp (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨hx,ht⟩)
    have hc := norm_cauchy hG₀ hgx
    have hc' : (∫t in Icc l r, ‖G₀ t‖*‖G (x,t)‖) ≤
        Real.sqrt E₀*Real.sqrt (E x) :=
      hc.trans (mul_le_mul (Real.sqrt_le_sqrt hE₀)
        (Real.sqrt_le_sqrt (henergy x hx)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    calc
      _ = M x*(∫t in Icc l r, ‖G₀ t‖*‖G (x,t)‖) := by
        rw [←MeasureTheory.integral_const_mul]
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with t
        dsimp [H]
        ring
      _ ≤ M x*(Real.sqrt E₀*Real.sqrt (E x)) :=
        mul_le_mul_of_nonneg_left hc' (hM0 x hx)
      _ = _ := by dsimp only [Pi.mul_apply]; ring
  calc
    _ ≤ _ := hle
    _ = B*(∫t in Icc l r, ‖P t‖*‖G₀ t‖) +
        ∫x in Icc a b, ∫t in Icc l r, H (x,t) := by
      rw [integral_add hbase hiH.integral_prod_right,
        MeasureTheory.integral_const_mul,←integral_integral_swap hiH]
    _ ≤ _ := by
      have hc := (norm_cauchy hP hG₀).trans (mul_le_mul
        (Real.sqrt_le_sqrt hEP) (Real.sqrt_le_sqrt hE₀)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      have hh := mul_le_mul_of_nonneg_left hc hB
      nlinarith

end OrdinaryCompactCauchy

end

end OAI
