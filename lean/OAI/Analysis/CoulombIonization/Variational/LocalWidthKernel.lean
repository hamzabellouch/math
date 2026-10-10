import Mathlib
import OAI.Analysis.CoulombIonization.Localization.PacketScale
import OAI.Analysis.CoulombIonization.Variational.MasterWidth

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_LocalWidthKernel_scope

open Set Metric
open scoped NNReal

lemma widthKernel_ne_zero_distance {t : Space → ℝ} (ht : ∀ x, 0 < t x)
    {h : Space → ℝ} (hs : Function.support h ⊆ closedBall 0 1)
    {x y : Space} (hx : widthKernel t h x y ≠ 0) : ‖x-y‖ ≤ t x := by
  have hh : h ((t x)⁻¹ • (y-x)) ≠ 0 := by
    intro H; exact hx (by simp [widthKernel,H])
  have hr := hs hh
  simp only [mem_closedBall,dist_zero_right,norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (ht x).le),norm_sub_rev y x] at hr
  rwa [inv_mul_eq_div,div_le_one (ht x)] at hr

lemma widthKernel_eq_zero_of_far {t : Space → ℝ} (ht : ∀ x, 0 < t x)
    {h : Space → ℝ} (hs : Function.support h ⊆ closedBall 0 1)
    {x y : Space} (hx : t x < ‖x-y‖) : widthKernel t h x y = 0 := by
  by_contra hn
  exact (not_le.mpr hx) (widthKernel_ne_zero_distance ht hs hn)

lemma widthKernel_support_local {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) (hp : ∀ x, 0 < t x) (hT : (T:ℝ) ≤ 1/2)
    {h : Space → ℝ} (hs : Function.support h ⊆ closedBall 0 1) (y : Space) :
    Function.support (fun x => widthKernel t h x y) ⊆ closedBall y (2*t y) := by
  intro x hx
  have ha := widthKernel_ne_zero_distance hp hs hx
  have hd := ht.dist_le_mul x y
  have hb : t x-t y ≤ (T:ℝ)*‖x-y‖ := by
    simpa only [Real.dist_eq,dist_eq_norm] using (le_abs_self (t x-t y)).trans hd
  have hc := mul_le_mul_of_nonneg_right hT (norm_nonneg (x-y))
  simp only [mem_closedBall,dist_eq_norm]
  linarith

lemma widthKernel_clamp {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) (hp : ∀ x, 0 < t x) (hT : (T:ℝ) ≤ 1)
    {h : Space → ℝ} (hs : Function.support h ⊆ closedBall 0 1) (y : Space) :
    (fun x => widthKernel t h x y) =
      (fun x => widthKernel (fun z => max (t z) (t y/2)) h x y) := by
  funext x
  by_cases hx : t y/2 ≤ t x
  · simp only [widthKernel,max_eq_left hx]
  have hx' : t x < t y/2 := lt_of_not_ge hx
  have hd := ht.dist_le_mul y x
  have hb : t y-t x ≤ (T:ℝ)*‖x-y‖ := by
    simpa only [Real.dist_eq,dist_eq_norm,norm_sub_rev y x] using (le_abs_self (t y-t x)).trans hd
  have hc := mul_le_mul_of_nonneg_right hT (norm_nonneg (x-y))
  have hf : t y/2 < ‖x-y‖ := by linarith
  have hz := widthKernel_eq_zero_of_far hp hs (hx'.trans hf)
  have hp' (z : Space) : 0 < max (t z) (t y/2) := (hp z).trans_le (le_max_left _ _)
  have hf' : max (t x) (t y/2) < ‖x-y‖ := by rwa [max_eq_right hx'.le]
  rw [hz,widthKernel_eq_zero_of_far hp' hs hf']

lemma widthKernel_local_lipschitz {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) (hp : ∀ x, 0 < t x) (hT : (T:ℝ) ≤ 1/2)
    {h : Space → ℝ} {H : ℝ≥0} (hh : LipschitzWith H h) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1) (y : Space) :
    LipschitzWith ⟨(24*M+24*(H:ℝ))*(t y)⁻¹^4, by positivity⟩
      (fun x => widthKernel t h x y) := by
  rw [widthKernel_clamp ht hp (by linarith) hs y]
  have hq : 0 < t y/2 := half_pos (hp y)
  have hl (x : Space) : t y/2 ≤ max (t x) (t y/2) := le_max_right _ _
  apply (widthKernel_lipschitz (ht.max_const (t y/2)) hq hl hh hM hb hs y).weaken
  change (3*M*(T:ℝ)+(H:ℝ)*(1+(T:ℝ)))*(t y/2)⁻¹^4 ≤
    (24*M+24*(H:ℝ))*(t y)⁻¹^4
  have hcoeff : 16*(3*M*(T:ℝ)+(H:ℝ)*(1+(T:ℝ))) ≤ 24*M+24*(H:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hT hM,mul_le_mul_of_nonneg_left hT H.coe_nonneg]
  have he : (t y/2)⁻¹^4 = 16*(t y)⁻¹^4 := by rw [inv_div]; ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (inv_nonneg.mpr (hp y).le) 4)]

end Work_LocalWidthKernel_scope

open MeasureTheory Set Metric
open scoped NNReal ContDiff

def masterKernel (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) : ℝ :=
  (scaledRealPacket (masterWidth c₁ r₀ s x) g (y-x))^2

lemma scaledRealPacket_sq {b : ℝ} (hb : 0 < b) (g : Space → ℝ) (z : Space) :
    (scaledRealPacket b g z)^2 = b⁻¹^3*(g (b⁻¹ • z))^2 := by
  have he : (b ^(-(3/2:ℝ)))^2 = b⁻¹^3 := by
    apply mul_right_cancel₀ (pow_ne_zero 3 hb.ne')
    rw [packetScale_factor hb,←mul_pow,inv_mul_cancel₀ hb.ne',one_pow]
  simp only [scaledRealPacket,mul_pow,he]

lemma masterKernel_eq_widthKernel {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) (g : Space → ℝ) :
    masterKernel c₁ r₀ s g = widthKernel (masterWidth c₁ r₀ s) (fun z => (g z)^2) := by
  funext x y
  exact scaledRealPacket_sq (masterWidth_pos hc hr hs x) g (y-x)

lemma masterKernel_nonneg (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    0 ≤ masterKernel c₁ r₀ s g x y := sq_nonneg _

lemma masterKernel_mass {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hgn : ∫ z, (g z)^2 = 1) (x : Space) :
    ∫ y, masterKernel c₁ r₀ s g x y = 1 := by
  unfold masterKernel
  rw [integral_sub_right_eq_self (fun z => (scaledRealPacket (masterWidth c₁ r₀ s x) g z)^2) x,
    scaledRealPacket_mass (masterWidth_pos hc hr hs x) g,hgn]

lemma masterKernel_smooth_eval (c₁ r₀ s : ℝ) {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (x : Space) : ContDiff ℝ ∞ (masterKernel c₁ r₀ s g x) :=
  ((scaledRealPacket_smooth _ hg).comp (contDiff_id.sub contDiff_const)).pow 2

lemma masterWidth_small_lipschitz {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) :
    LipschitzWith (1/2) (masterWidth c₁ r₀ s) := by
  apply (masterWidth_lipschitz hc.le hr hs).weaken
  change c₁*(1+masterExponent)*s^masterExponent ≤ (1/2:ℝ)
  have hp := Real.rpow_le_one hs.le hs1 masterExponent_nonneg
  have hcp : 0 ≤ c₁*(1+masterExponent) := mul_nonneg hc.le (by linarith [masterExponent_pos])
  calc
    _ ≤ c₁*(1+masterExponent)*1 := mul_le_mul_of_nonneg_left hp hcp
    _ ≤ _ := by norm_num [masterExponent] at *; nlinarith

lemma masterKernel_joint_continuous {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) :
    Continuous (fun p : Space × Space => masterKernel c₁ r₀ s g p.1 p.2) := by
  rw [masterKernel_eq_widthKernel hc hr hs g]
  have ht := (masterWidth_lipschitz hc.le hr hs).continuous.comp (continuous_fst : Continuous (Prod.fst : Space × Space → Space))
  have hi := ht.inv₀ (fun p => (masterWidth_pos hc hr hs p.1).ne')
  exact (hi.pow 3).mul ((hg.pow 2).comp (hi.smul (continuous_snd.sub continuous_fst)))

lemma masterProfile_support {g : Space → ℝ} (hgs : tsupport g ⊆ ball 0 1) :
    Function.support (fun z => (g z)^2) ⊆ closedBall 0 1 := by
  intro z hz
  have hg : g z ≠ 0 := by intro H; exact hz (by simp [H])
  exact ball_subset_closedBall (hgs (subset_tsupport g hg))

theorem masterKernel_uniform_test_constants {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (c₁ r₀ s : ℝ),
      0 < c₁ → c₁ < (10*(100000:ℝ))⁻¹ → 0 < r₀ → 0 < s → s ≤ 1 →
      ∀ y : Space,
      Function.support (fun x => masterKernel c₁ r₀ s g x y) ⊆
        closedBall y (2*masterWidth c₁ r₀ s y) ∧
      LipschitzWith ⟨(C:ℝ)*(masterWidth c₁ r₀ s y)⁻¹^4, by positivity⟩
        (fun x => masterKernel c₁ r₀ s g x y) := by
  have hp := masterProfile_support hgs
  have hcomp : HasCompactSupport (fun z => (g z)^2) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) 1) hp
  obtain ⟨H,hH⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcomp (hg.pow 2) (by simp)
  obtain ⟨z₀,hz₀⟩ := (hg.continuous.pow 2).norm.exists_forall_ge_of_hasCompactSupport hcomp.norm
  let M := ‖(g z₀)^2‖
  have hM : 0 ≤ M := norm_nonneg _
  refine ⟨⟨24*M+24*(H:ℝ)+1,by positivity⟩,?_,?_⟩
  · change (0:ℝ) < 24*M+24*(H:ℝ)+1
    positivity
  intro c₁ r₀ s hc hcL hr hs hs1 y
  rw [masterKernel_eq_widthKernel hc hr hs g]
  have ht := masterWidth_small_lipschitz hc hcL hr hs hs1
  have hpos := masterWidth_pos hc hr hs
  refine ⟨widthKernel_support_local ht hpos (by norm_num) hp y,?_⟩
  apply (widthKernel_local_lipschitz ht hpos (by norm_num) hH hM hz₀ hp y).weaken
  change (24*M+24*(H:ℝ))*(masterWidth c₁ r₀ s y)⁻¹^4 ≤
    (24*M+24*(H:ℝ)+1)*(masterWidth c₁ r₀ s y)⁻¹^4
  exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (inv_nonneg.mpr (hpos y).le) 4)

end CoulombAtom

end

end OAI
