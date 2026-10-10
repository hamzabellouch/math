import Mathlib
import OAI.Probability.SKRatio.Variational.ScalarHilbert

namespace OAI

noncomputable section
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

def a (β : ℝ) : ℝ := ∫ h, v h ∂fieldLaw β

def l (β : ℝ) : ℝ := ∫ h, multiplier h ∂fieldLaw β

def G (β : ℝ) : ℝ := ∫ h, g h ∂fieldLaw β

def R (β : ℝ) : ℝ := ∫ h, rho h ∂fieldLaw β

lemma l_eq (β : ℝ) : l β = 64/100-(19/100)*a β := mean_multiplier β
lemma l_pos (β : ℝ) : 0 < l β := mean_multiplier_pos _
lemma a_nonneg (β : ℝ) : 0 ≤ a β := integral_nonneg (fun h => (v_pos h).le)
lemma a_le_one (β : ℝ) : a β ≤ 1 := by
  have h := integral_mono (memLp_v.integrable (by norm_num : (1:ENNReal) ≤ 2))
    (integrable_const (μ := fieldLaw β) 1) v_le_one
  simpa only [a,integral_const,probReal_univ,smul_eq_mul,one_mul] using h
lemma l_lower (β : ℝ) : 45/100 ≤ l β := by
  rw [l_eq]
  linarith [a_le_one β]
lemma R_nonneg (β : ℝ) : 0 ≤ R β := integral_rho_nonneg

def F (β : ℝ) (h : ℝ) : ℝ :=
  (v h+a β)*h + 2*β^2*m h*v h + (50/100-β^2*a β/l β)*v h +
    (12/100)*m h + 3*β^2*G β*g h

def U₀ (β : ℝ) : ℝ := l β+18/1000+
  β^2*(a β^2/l β-a β-(3/2)*G β^2)-β^2*R β

def U₁ (β : ℝ) : ℝ := (4644/10000)-β*sd (fieldLaw β) v/2+
  β^2*(∫ h, m h*v h ∂fieldLaw β)-
    β^2*((3/2)*sd (fieldLaw β) g^2+R β)

lemma multiplier_affine_v (h : ℝ) :
    multiplier h = (70/100)-(1/4)*v h-(6/100)*m h := by
  unfold multiplier v
  ring

lemma memLp_F (β : ℝ) : MemLp (F β) 2 (fieldLaw β) := by
  convert! (((((memLp_field_v β).add ((memLp_field β).const_mul (a β))).add
      (memLp_mv.const_mul (2*β^2))).add (memLp_v.const_mul (50/100-β^2*a β/l β))).add
      (memLp_m.const_mul (12/100:ℝ))).add (memLp_g.const_mul (3*β^2*G β)) using 1
  ext h
  dsimp [F]
  ring

lemma integral_F_pairing (β : ℝ) {b : ℝ → ℝ} (hb : MemLp b 2 (fieldLaw β)) :
    ∫ h, b h*F β h ∂fieldLaw β =
      (∫ h, b h*(h*v h) ∂fieldLaw β)+a β*(∫ h, b h*h ∂fieldLaw β)+
      (2*β^2)*(∫ h, b h*(m h*v h) ∂fieldLaw β)+
      (50/100-β^2*a β/l β)*(∫ h, b h*v h ∂fieldLaw β)+
      (12/100)*(∫ h, b h*m h ∂fieldLaw β)+
      (3*β^2*G β)*(∫ h, b h*g h ∂fieldLaw β) := by
  have ihv : Integrable (fun h => b h*(h*v h)) (fieldLaw β) := hb.integrable_mul (memLp_field_v β)
  have ih : Integrable (fun h => b h*h) (fieldLaw β) := hb.integrable_mul (memLp_field β)
  have imv : Integrable (fun h => b h*(m h*v h)) (fieldLaw β) := hb.integrable_mul (memLp_mv (p := 2))
  have iv : Integrable (fun h => b h*v h) (fieldLaw β) := hb.integrable_mul (memLp_v (p := 2))
  have im : Integrable (fun h => b h*m h) (fieldLaw β) := hb.integrable_mul (memLp_m (p := 2))
  have ig : Integrable (fun h => b h*g h) (fieldLaw β) := hb.integrable_mul memLp_g
  have he (h : ℝ) : b h*F β h =
      b h*(h*v h)+a β*(b h*h)+(2*β^2)*(b h*(m h*v h))+
      (50/100-β^2*a β/l β)*(b h*v h)+(12/100)*(b h*m h)+
      (3*β^2*G β)*(b h*g h) := by unfold F; ring
  simp_rw [he]
  have i1 : Integrable (fun h => b h*(h*v h)+a β*(b h*h)) (fieldLaw β) :=
    ihv.add (ih.const_mul _)
  have i2 : Integrable (fun h => b h*(h*v h)+a β*(b h*h)+(2*β^2)*(b h*(m h*v h)))
      (fieldLaw β) := i1.add (imv.const_mul _)
  have i3 : Integrable (fun h => b h*(h*v h)+a β*(b h*h)+(2*β^2)*(b h*(m h*v h))+
      (50/100-β^2*a β/l β)*(b h*v h)) (fieldLaw β) := i2.add (iv.const_mul _)
  have i4 : Integrable (fun h => b h*(h*v h)+a β*(b h*h)+(2*β^2)*(b h*(m h*v h))+
      (50/100-β^2*a β/l β)*(b h*v h)+(12/100)*(b h*m h)) (fieldLaw β) :=
    i3.add (im.const_mul _)
  rw [integral_add i4 (ig.const_mul _),integral_add i3 (im.const_mul _),
    integral_add i2 (iv.const_mul _),integral_add i1 (imv.const_mul _),
    integral_add ihv (ih.const_mul _)]
  simp only [integral_const_mul]

lemma integral_mean_zero_multiplier (β : ℝ) {b : ℝ → ℝ}
    (hb : MemLp b 2 (fieldLaw β)) (hmean : ∫ h, b h ∂fieldLaw β = 0) :
    ∫ h, b h*multiplier h ∂fieldLaw β =
      -(1/4)*(∫ h, b h*v h ∂fieldLaw β)-(6/100)*(∫ h, b h*m h ∂fieldLaw β) := by
  have ib := hb.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have iv : Integrable (fun h => b h*v h) (fieldLaw β) := hb.integrable_mul (memLp_v (p := 2))
  have im : Integrable (fun h => b h*m h) (fieldLaw β) := hb.integrable_mul (memLp_m (p := 2))
  have he (h : ℝ) : b h*multiplier h =
      (70/100)*b h-(1/4)*(b h*v h)-(6/100)*(b h*m h) := by
    rw [multiplier_affine_v]
    ring
  simp_rw [he]
  have i1 : Integrable (fun h => (70/100)*b h-(1/4)*(b h*v h)) (fieldLaw β) :=
    (ib.const_mul _).sub (iv.const_mul _)
  rw [integral_sub i1 (im.const_mul _),integral_sub (ib.const_mul _) (iv.const_mul _)]
  simp only [integral_const_mul,hmean,mul_zero,zero_sub,neg_mul]

lemma mean_field (β : ℝ) : ∫ h, h ∂fieldLaw β = β^2 := integral_id_gaussianReal

lemma sd_field {β : ℝ} (hβ : 0 ≤ β) : sd (fieldLaw β) (fun h => h) = β := by
  have hh := variance_id_gaussianReal (μ := β^2) (v := variance β)
  rw [variance_eq_integral measurable_id.aemeasurable] at hh
  change ∫ h, (h-(∫ t, t ∂fieldLaw β))^2 ∂fieldLaw β = _ at hh
  rw [variance_coe] at hh
  unfold sd l2Norm centered
  rw [hh,sqrt_sq hβ]

lemma field_centered_covariance (β : ℝ) :
    ∫ h, centered (fieldLaw β) (fun t => t) h*centered (fieldLaw β) v h ∂fieldLaw β =
      -2*β^2*(∫ h, m h*v h ∂fieldLaw β) := by
  have hm := integral_centered (memLp_field β)
  rw [pairing_centered (memLp_centered (memLp_field β)) memLp_v hm]
  have he := coherent_paired_expansion β (memLp_const (1:ℝ))
  simp only [one_mul,field_variance_identity] at he
  have hd := integral_mul_decomposition (memLp_field β) (memLp_v (p := 2))
  rw [mean_field] at hd
  linarith only [he,hd]

lemma centered_field_v_rank_bound {β : ℝ} (hβ : 0 ≤ β) {b : ℝ → ℝ}
    (hb : MemLp b 2 (fieldLaw β)) (hmean : ∫ h, b h ∂fieldLaw β = 0) :
    (∫ h, b h*h ∂fieldLaw β)*(∫ h, b h*v h ∂fieldLaw β) ≤
      (β*sd (fieldLaw β) v/2-β^2*(∫ h, m h*v h ∂fieldLaw β))*
        (∫ h, b h^2 ∂fieldLaw β) := by
  have h := rank_two_bound hb (memLp_centered (memLp_field β))
    (memLp_centered (memLp_v (p := 2)))
  rw [pairing_centered hb (memLp_field β) hmean,
    pairing_centered hb memLp_v hmean,field_centered_covariance] at h
  change _ ≤ ((sd (fieldLaw β) (fun h => h)*sd (fieldLaw β) v+
    -2*β^2*(∫ h, m h*v h ∂fieldLaw β))/2)*_ at h
  rw [sd_field hβ] at h
  convert! h using 1
  ring

section WeightedSquare
variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma integrable_multiplier_translate_square {b : ℝ → ℝ} (hb : MemLp b 2 μ) (c : ℝ) :
    Integrable (fun h => (multiplier h+c)*b h^2) μ := by
  simp_rw [add_mul]
  exact (integrable_multiplier_square hb).add (hb.integrable_sq.const_mul c)

lemma weighted_square_centered {b : ℝ → ℝ} (hb : MemLp b 2 μ) (c : ℝ) :
    ∫ h, (multiplier h+c)*b h^2 ∂μ =
      (∫ h, b h ∂μ)^2*((∫ h, multiplier h ∂μ)+c)+
      (2*(∫ h, b h ∂μ))*(∫ h, centered μ b h*multiplier h ∂μ)+
      (∫ h, (multiplier h+c)*centered μ b h^2 ∂μ) := by
  let A := ∫ h, b h ∂μ
  let b₀ := centered μ b
  have hb0 : MemLp b₀ 2 μ := memLp_centered hb
  have hbI := hb0.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hL : Integrable (fun h => b₀ h*multiplier h) μ := hb0.integrable_mul memLp_multiplier
  have hI := integrable_multiplier_translate_square hb0 c
  have iL : Integrable multiplier μ := integrable_multiplier μ
  have he (h : ℝ) : (multiplier h+c)*b h^2 =
      A^2*(multiplier h+c)+(2*A)*(b₀ h*multiplier h)+(2*A*c)*b₀ h+
        (multiplier h+c)*b₀ h^2 := by dsimp [A,b₀,centered]; ring
  simp_rw [he]
  have i1 : Integrable (fun h => A^2*(multiplier h+c)) μ :=
    (iL.add (integrable_const c)).const_mul _
  have i2 : Integrable (fun h => A^2*(multiplier h+c)+(2*A)*(b₀ h*multiplier h)) μ :=
    i1.add (hL.const_mul _)
  have i3 : Integrable (fun h => A^2*(multiplier h+c)+(2*A)*(b₀ h*multiplier h)+
      (2*A*c)*b₀ h) μ := i2.add (hbI.const_mul _)
  rw [integral_add i3 hI,integral_add i2 (hbI.const_mul _),integral_add i1 (hL.const_mul _)]
  simp only [integral_const_mul]
  rw [integral_add iL (integrable_const c),integral_const]
  simp only [probReal_univ,smul_eq_mul,one_mul,show (∫ h, b₀ h ∂μ) = 0 from integral_centered hb,
    mul_zero,add_zero]
  rfl

omit [IsProbabilityMeasure μ] in
lemma weighted_square_floor {b : ℝ → ℝ} (hb : MemLp b 2 μ) (c : ℝ) :
    (4464/10000+c)*(∫ h, b h^2 ∂μ) ≤ ∫ h, (multiplier h+c)*b h^2 ∂μ := by
  rw [←integral_const_mul]
  apply integral_mono (hb.integrable_sq.const_mul _) (integrable_multiplier_translate_square hb c)
  intro h
  exact mul_le_mul_of_nonneg_right (by linarith [multiplier_pos h]) (sq_nonneg _)

end WeightedSquare

def coherentUpper (β : ℝ) (b : ℝ → ℝ) : ℝ :=
  (∫ h, b h*h ∂fieldLaw β)*(∫ h, b h*v h ∂fieldLaw β)+
  (∫ h, b h ∂fieldLaw β)*(∫ h, b h*((h-β^2+2*β^2*m h)*v h) ∂fieldLaw β)+
  β^2*((3/2)*(∫ h, b h*g h ∂fieldLaw β)^2+R β*(∫ h, b h^2 ∂fieldLaw β))-
  β^2/(4*l β)*((∫ h, b h*v h ∂fieldLaw β)+a β*(∫ h, b h ∂fieldLaw β))^2

lemma coherent_le_upper (β : ℝ) {b : ℝ → ℝ} (hb : MemLp b 2 (fieldLaw β)) :
    coherent β b ≤ coherentUpper β b := by
  have h := mul_le_mul_of_nonneg_left (kernel_bound hb) (sq_nonneg β)
  unfold coherent coherentUpper a l R
  linarith only [h]

lemma memLp_stein_v (β : ℝ) :
    MemLp (fun h => (h-β^2+2*β^2*m h)*v h) 2 (fieldLaw β) := by
  convert! ((memLp_field_v β).sub (memLp_v.const_mul (β^2))).add
    (memLp_mv.const_mul (2*β^2)) using 1
  ext h
  dsimp
  ring

theorem coherent_full_expansion (β : ℝ) {b : ℝ → ℝ} (hb : MemLp b 2 (fieldLaw β)) :
    let A := ∫ h, b h ∂fieldLaw β
    let b₀ := centered (fieldLaw β) b
    coherentUpper β b-(∫ h, (multiplier h+18/1000)*b h^2 ∂fieldLaw β) =
      -U₀ β*A^2 + A*(∫ h, b₀ h*F β h ∂fieldLaw β)+
      (∫ h, b₀ h*h ∂fieldLaw β)*(∫ h, b₀ h*v h ∂fieldLaw β)+
      (3/2)*β^2*(∫ h, b₀ h*g h ∂fieldLaw β)^2+
      β^2*R β*(∫ h, b₀ h^2 ∂fieldLaw β)-
      β^2/(4*l β)*(∫ h, b₀ h*v h ∂fieldLaw β)^2-
      (∫ h, (multiplier h+18/1000)*b₀ h^2 ∂fieldLaw β) := by
  dsimp only
  have hb0 := memLp_centered hb
  have hmean := integral_centered hb
  have hdH := integral_mul_decomposition hb (memLp_field β)
  have hdV := integral_mul_decomposition hb (memLp_v (p := 2))
  have hdG := integral_mul_decomposition hb memLp_g
  have hdT := integral_mul_decomposition hb (memLp_stein_v β)
  rw [field_variance_identity,mul_zero,zero_add] at hdT
  rw [mean_field] at hdH
  unfold coherentUpper
  rw [hdH,hdV,hdG,hdT,l2_decomposition hb,weighted_square_centered hb,
    integral_F_pairing β hb0,coherent_paired_expansion β hb0,
    integral_mean_zero_multiplier β hb0 hmean]
  unfold U₀ a l G
  field_simp
  ring

theorem coherent_two_dimensional {β : ℝ} (hβ : 0 ≤ β) {b : ℝ → ℝ}
    (hb : MemLp b 2 (fieldLaw β)) :
    let A := ∫ h, b h ∂fieldLaw β
    let b₀ := centered (fieldLaw β) b
    coherent β b-(∫ h, (multiplier h+18/1000)*b h^2 ∂fieldLaw β) ≤
      -U₀ β*A^2-U₁ β*(∫ h, b₀ h^2 ∂fieldLaw β)+A*(∫ h, b₀ h*F β h ∂fieldLaw β) := by
  dsimp only
  have hb0 := memLp_centered hb
  have hmean := integral_centered hb
  have hform := coherent_le_upper β hb
  have hexp := coherent_full_expansion β hb
  dsimp only at hexp
  have hHV := centered_field_v_rank_bound hβ hb0 hmean
  have hG := mul_le_mul_of_nonneg_left (pairing_centered_sq_le hb0 memLp_g hmean)
    (show 0 ≤ (3/2:ℝ)*β^2 by positivity)
  have hL := weighted_square_floor hb0 (18/1000)
  have hneg : 0 ≤ β^2/(4*l β)*(∫ h, centered (fieldLaw β) b h*v h ∂fieldLaw β)^2 :=
    mul_nonneg (div_nonneg (sq_nonneg β) (by positivity [l_pos β])) (sq_nonneg _)
  unfold U₁
  nlinarith only [hform,hexp,hHV,hG,hL,hneg]

lemma quadratic_slack_bound {u₀ u₁ s A t : ℝ} (hu : 0 < u₀) (_ht : 0 ≤ t)
    (_hs : 0 ≤ s) (hdisc : s^2 ≤ 4*u₀*u₁) :
    -u₀*A^2-u₁*t^2+abs A*s*t ≤ 0 := by
  have hsq := sq_nonneg (2*u₀*abs A-s*t)
  have hd := mul_le_mul_of_nonneg_right hdisc (sq_nonneg t)
  have he : (2*u₀*abs A-s*t)^2 = 4*u₀^2*A^2-4*u₀*abs A*s*t+s^2*t^2 := by
    ring_nf
    rw [sq_abs]
  rw [he] at hsq
  apply (mul_le_mul_iff_of_pos_left (show 0 < 4*u₀ by positivity)).mp
  nlinarith only [hsq,hd]

theorem coherent_bound_of_slacks {β : ℝ} (hβ : 0 ≤ β)
    (hU₀ : 0 < U₀ β) (hdisc : sd (fieldLaw β) (F β)^2 ≤ 4*U₀ β*U₁ β)
    {b : ℝ → ℝ} (hb : MemLp b 2 (fieldLaw β)) :
    coherent β b ≤ ∫ h, (multiplier h+18/1000)*b h^2 ∂fieldLaw β := by
  have htwo := coherent_two_dimensional hβ hb
  dsimp only at htwo
  let A := ∫ h, b h ∂fieldLaw β
  let b₀ := centered (fieldLaw β) b
  let t := l2Norm (fieldLaw β) b₀
  let s := sd (fieldLaw β) (F β)
  have hb0 : MemLp b₀ 2 (fieldLaw β) := memLp_centered hb
  have hs : 0 ≤ s := sd_nonneg _
  have ht : 0 ≤ t := l2Norm_nonneg _
  have ht2 : t^2 = ∫ h, b₀ h^2 ∂fieldLaw β := l2Norm_sq _
  have hcs := abs_pairing_centered_le hb0 (memLp_F β) (integral_centered hb)
  have hcross : A*(∫ h, b₀ h*F β h ∂fieldLaw β) ≤ abs A*s*t := by
    calc
      _ ≤ |A*(∫ h, b₀ h*F β h ∂fieldLaw β)| := le_abs_self _
      _ = abs A*|∫ h, b₀ h*F β h ∂fieldLaw β| := abs_mul _ _
      _ ≤ abs A*(t*s) := mul_le_mul_of_nonneg_left hcs (abs_nonneg _)
      _ = _ := by ring
  have hq := quadratic_slack_bound (A := A) hU₀ ht hs hdisc
  rw [ht2] at hq
  change coherent β b-_ ≤ -U₀ β*A^2-U₁ β*(∫ h, b₀ h^2 ∂fieldLaw β)+
    A*(∫ h, b₀ h*F β h ∂fieldLaw β) at htwo
  linarith only [htwo,hcross,hq]

end SKRatio.Scalar

end

end OAI
