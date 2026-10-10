import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.CoulombLipschitzDuality
import OAI.Analysis.CoulombIonization.Variational.LocalWidthKernel

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_WidthKernelAmplitude_scope

open Set Metric
open scoped NNReal

lemma scaledDensity_active_width_error {q a b : ℝ} (hq : 0 < q)
    (ha : q ≤ a) (hb : q ≤ b) {h : Space → ℝ} {H : ℝ≥0}
    (hh : LipschitzWith H h) {M : ℝ} (_hM : 0 ≤ M)
    (hbound : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1)
    (z : Space) (hz : h (a⁻¹ • z) ≠ 0) :
    ‖a⁻¹^3*h (a⁻¹ • z)-b⁻¹^3*h (b⁻¹ • z)‖ ≤
      (3*M+(H:ℝ))*q⁻¹^4*‖a-b‖ := by
  have hap := hq.trans_le ha
  have hbp := hq.trans_le hb
  have hn : ‖a⁻¹ • z‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hs hz
  have he : a⁻¹ • z-b⁻¹ • z = (b⁻¹*(b-a)) • (a⁻¹ • z) := by
    rw [smul_smul,←sub_smul]
    congr 1
    field_simp
  have hd : ‖a⁻¹ • z-b⁻¹ • z‖ ≤ q⁻¹*‖a-b‖ := by
    rw [he,norm_smul,norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hbp.le),norm_sub_rev b a]
    calc
      _ ≤ (b⁻¹*‖a-b‖)*1 := mul_le_mul_of_nonneg_left hn (by positivity)
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_right (inv_anti₀ hq hb) (norm_nonneg (a-b))
  have hdiff := hh.dist_le_mul (a⁻¹ • z) (b⁻¹ • z)
  simp only [dist_eq_norm] at hdiff
  have hdiff' := hdiff.trans (mul_le_mul_of_nonneg_left hd H.coe_nonneg)
  have hi : ‖b⁻¹^3‖ ≤ q⁻¹^3 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hbp.le) _)]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hbp.le) (inv_anti₀ hq hb) 3
  have hid := invCube_norm_sub_le hq ha hb
  have halg : a⁻¹^3*h (a⁻¹ • z)-b⁻¹^3*h (b⁻¹ • z) =
      (a⁻¹^3-b⁻¹^3)*h (a⁻¹ • z)+b⁻¹^3*(h (a⁻¹ • z)-h (b⁻¹ • z)) := by ring
  rw [halg]
  calc
    _ ≤ ‖(a⁻¹^3-b⁻¹^3)*h (a⁻¹ • z)‖+‖b⁻¹^3*(h (a⁻¹ • z)-h (b⁻¹ • z))‖ := norm_add_le _ _
    _ = ‖a⁻¹^3-b⁻¹^3‖*‖h (a⁻¹ • z)‖+‖b⁻¹^3‖*‖h (a⁻¹ • z)-h (b⁻¹ • z)‖ := by rw [norm_mul,norm_mul]
    _ ≤ (3*q⁻¹^4*‖a-b‖)*M+(q⁻¹^3)*((H:ℝ)*(q⁻¹*‖a-b‖)) :=
      add_le_add (mul_le_mul hid (hbound _) (norm_nonneg _) (by positivity))
        (mul_le_mul hi hdiff' (norm_nonneg _) (by positivity))
    _ = _ := by ring

lemma scaledDensity_width_error {q a b : ℝ} (hq : 0 < q)
    (ha : q ≤ a) (hb : q ≤ b) {h : Space → ℝ} {H : ℝ≥0}
    (hh : LipschitzWith H h) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1)
    (z : Space) :
    ‖a⁻¹^3*h (a⁻¹ • z)-b⁻¹^3*h (b⁻¹ • z)‖ ≤
      (3*M+(H:ℝ))*q⁻¹^4*‖a-b‖ := by
  by_cases hz : h (a⁻¹ • z) ≠ 0
  · exact scaledDensity_active_width_error hq ha hb hh hM hbound hs z hz
  by_cases hz' : h (b⁻¹ • z) ≠ 0
  · simpa only [norm_sub_rev b a,norm_sub_rev (b⁻¹^3*h (b⁻¹ • z)) _] using
      scaledDensity_active_width_error hq hb ha hh hM hbound hs z hz'
  simp only [not_ne_iff] at hz hz'
  simp only [hz,hz',mul_zero,sub_zero,norm_zero]
  positivity

theorem widthKernel_freeze_error {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) (hp : ∀ x, 0 < t x) (hT : (T:ℝ) ≤ 1/2)
    {h : Space → ℝ} {H : ℝ≥0} (hh : LipschitzWith H h) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1)
    (y x : Space) :
    ‖widthKernel t h x y-widthKernel (fun _ => t y) h x y‖ ≤
      32*(3*M+(H:ℝ))*(T:ℝ)*(t y)⁻¹^3 := by
  have hty := hp y
  by_cases hd : ‖x-y‖ ≤ 2*t y
  · have hcl := congrFun (widthKernel_clamp ht hp (by linarith) hs y) x
    rw [hcl]
    have hq : 0 < t y/2 := half_pos (hp y)
    have hby : t y/2 ≤ t y := by linarith [hp y]
    have hh' := scaledDensity_width_error hq (le_max_right (t x) (t y/2)) hby hh hM hbound hs (y-x)
    have htd := (ht.max_const (t y/2)).dist_le_mul x y
    simp only [max_eq_left hby,dist_eq_norm] at htd
    have hd' := htd.trans (mul_le_mul_of_nonneg_left hd T.coe_nonneg)
    have hcoeff : 0 ≤ (3*M+(H:ℝ))*(t y/2)⁻¹^4 := by positivity
    apply hh'.trans
    calc
      _ ≤ ((3*M+(H:ℝ))*(t y/2)⁻¹^4)*((T:ℝ)*(2*t y)) := mul_le_mul_of_nonneg_left hd' hcoeff
      _ = _ := by field_simp [(hp y).ne']; ring
  · have hv : widthKernel t h x y = 0 := by
      by_contra hn
      exact hd (by simpa only [mem_closedBall,dist_eq_norm] using widthKernel_support_local ht hp hT hs y hn)
    have hf : widthKernel (fun _ => t y) h x y = 0 :=
      widthKernel_eq_zero_of_far (fun _ => hp y) hs (by linarith [lt_of_not_ge hd,hp y])
    rw [hv,hf,sub_self,norm_zero]
    positivity

end Work_WidthKernelAmplitude_scope

open MeasureTheory Set Metric
open scoped NNReal ContDiff

open CoulombAnalysis

lemma widthKernel_frozen_mass {b : ℝ} (hb : 0 < b) (h : Space → ℝ) (y : Space) :
    (∫ x, widthKernel (fun _ => b) h x y) = ∫ x, h x := by
  unfold widthKernel
  rw [integral_sub_left_eq_self (fun z => b⁻¹^3*h (b⁻¹ • z)) volume y,
    integral_const_mul,Measure.integral_comp_inv_smul_of_nonneg volume h hb.le,
    space_finrank,smul_eq_mul,←mul_assoc,←mul_pow,inv_mul_cancel₀ hb.ne',one_pow,one_mul]

lemma widthKernel_integrable {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) (hp : ∀ x, 0 < t x) (hT : (T:ℝ) ≤ 1/2)
    {h : Space → ℝ} {H : ℝ≥0} (hh : LipschitzWith H h) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1) (y : Space) :
    Integrable (fun x => widthKernel t h x y) := by
  apply (widthKernel_local_lipschitz ht hp hT hh hM hbound hs y).continuous.integrable_of_hasCompactSupport
  exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall y (2*t y))
    (widthKernel_support_local ht hp hT hs y)

theorem widthKernel_mass_error {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) (hp : ∀ x, 0 < t x) (hT : (T:ℝ) ≤ 1/2)
    {h : Space → ℝ} {H : ℝ≥0} (hh : LipschitzWith H h) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1) (y : Space) :
    ‖(∫ x, widthKernel t h x y)-(∫ x, h x)‖ ≤
      ((1024/3:ℝ)*Real.pi*(3*M+(H:ℝ)))*(T:ℝ) := by
  have hty := hp y
  have hk := widthKernel_integrable ht hp hT hh hM hbound hs y
  have hconst : LipschitzWith 0 (fun _ : Space => t y) := LipschitzWith.const _
  have hk0 := widthKernel_integrable hconst (fun _ => hp y) (by norm_num) hh hM hbound hs y
  rw [←widthKernel_frozen_mass hty h y,←integral_sub hk hk0]
  have hs0 := widthKernel_support_local hconst (fun _ => hp y) (by norm_num) hs y
  have hs1 := widthKernel_support_local ht hp hT hs y
  have he : (∫ x in closedBall y (2*t y), widthKernel t h x y-widthKernel (fun _ => t y) h x y) =
      ∫ x, widthKernel t h x y-widthKernel (fun _ => t y) h x y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have h1 : widthKernel t h x y = 0 := by
      by_contra hn; exact hx (hs1 hn)
    have h0 : widthKernel (fun _ => t y) h x y = 0 := by
      by_contra hn; exact hx (hs0 hn)
    rw [h1,h0,sub_self]
  rw [←he]
  have hh' := norm_setIntegral_le_of_norm_le_const
    ((isCompact_closedBall y (2*t y)).measure_lt_top (μ := volume))
    (fun x (_ : x ∈ closedBall y (2*t y)) => widthKernel_freeze_error ht hp hT hh hM hbound hs y x)
  apply hh'.trans_eq
  rw [Measure.addHaar_real_closedBall_center volume,tfSpace_closedBall_real (2*t y) (by positivity)]
  field_simp [hty.ne']
  ring

theorem masterKernel_approximate_mass {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1)
    (hgn : ∫ x : Space, (g x)^2 = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c₁ r₀ s : ℝ),
      0 < c₁ → c₁ < (10*(100000:ℝ))⁻¹ → 0 < r₀ → 0 < s → s ≤ 1 →
      ∀ y : Space, ‖(∫ x, masterKernel c₁ r₀ s g x y)-1‖ ≤ C*c₁*s^masterExponent := by
  have hp := masterProfile_support hgs
  have hcomp : HasCompactSupport (fun z => (g z)^2) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) 1) hp
  obtain ⟨H,hH⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcomp (hg.pow 2) (by simp)
  obtain ⟨z₀,hz₀⟩ := (hg.continuous.pow 2).norm.exists_forall_ge_of_hasCompactSupport hcomp.norm
  let M := ‖(g z₀)^2‖
  have hM : 0 ≤ M := norm_nonneg _
  let A := (1024/3:ℝ)*Real.pi*(3*M+(H:ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hw := masterExponent_pos
  refine ⟨A*(1+masterExponent)+1,by positivity,?_⟩
  intro c₁ r₀ s hc hcL hr hs hs1 y
  rw [masterKernel_eq_widthKernel hc hr hs g]
  have hT : c₁*(1+masterExponent)*s^masterExponent ≤ (1/2:ℝ) := by
    have hsp := Real.rpow_le_one hs.le hs1 masterExponent_nonneg
    have hcp : 0 ≤ c₁*(1+masterExponent) := by positivity
    calc
      _ ≤ c₁*(1+masterExponent)*1 := mul_le_mul_of_nonneg_left hsp hcp
      _ ≤ _ := by norm_num [masterExponent] at *; nlinarith
  have hh := widthKernel_mass_error (masterWidth_lipschitz hc.le hr hs)
    (masterWidth_pos hc hr hs) hT hH hM hz₀ hp y
  change _ ≤ A*(c₁*(1+masterExponent)*s^masterExponent) at hh
  rw [hgn] at hh
  apply hh.trans
  have hn : 0 ≤ c₁*s^masterExponent := by positivity
  nlinarith only [hn]

end CoulombAtom

end

end OAI
