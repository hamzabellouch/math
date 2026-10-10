import Mathlib
import OAI.Geometry.SmoothYau.Estimates.RadialLeadingTrace
import OAI.Geometry.SmoothYau.Estimates.RadialTraceAbsorption
import OAI.Geometry.SmoothYau.Estimates.RadialTransitionPositive
import OAI.Geometry.SmoothYau.Limits.CompactFullProfileMargin

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma radial_norm_gain {a d : E} (had : inner ℝ a d = 0) (q : ℝ) :
    ‖a + q • d‖^2 = ‖a‖^2 + q^2 * ‖d‖^2 := by
  rw [norm_add_sq_real]
  simp [inner_smul_right,had,norm_smul, mul_pow]

theorem radial_gradient_no_loss (a r e : E) (had : inner ℝ a r = 0)
    (q ε : ℝ) (he : ‖e‖ ≤ ε*‖a‖) :
    (1-ε)*‖a‖ ≤ ‖a+q • r+e‖ := by
  have hsq := radial_norm_gain had q
  have hnorm : ‖a‖ ≤ ‖a+q • r‖ := by
    nlinarith [norm_nonneg a,norm_nonneg (a+q • r),mul_nonneg (sq_nonneg q) (sq_nonneg ‖r‖)]
  have htri : ‖a+q • r‖ ≤ ‖a+q • r+e‖+‖e‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (a+q • r+e) e
  linarith

theorem radial_gradient_annular_gain (a r e : E) (had : inner ℝ a r = 0)
    (δ A f c ε : ℝ) (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hf : c ≤ f)
    (hA : ‖a‖/2 ≤ A) (hr : (1:ℝ)/2 ≤ ‖r‖) (he : ‖e‖ ≤ ε*‖a‖) :
    (Real.sqrt (1+δ^2*c^2/16)-ε)*‖a‖ ≤ ‖a+(δ*A*f) • r+e‖ := by
  have hA0 : 0 ≤ A := (div_nonneg (norm_nonneg a) (by norm_num)).trans hA
  have hq : δ*‖a‖*c/2 ≤ δ*A*f := by
    have h1 := mul_le_mul_of_nonneg_right hA hc
    have h2 := mul_le_mul_of_nonneg_left hf hA0
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hδ
    nlinarith only [h3]
  have hq0 : 0 ≤ δ*‖a‖*c/2 := by positivity
  have hq2 := (sq_le_sq₀ hq0 (hq0.trans hq)).mpr hq
  have hr2 : (1:ℝ)/4 ≤ ‖r‖^2 := by nlinarith
  have hp := mul_le_mul hq2 hr2 (by norm_num : (0:ℝ) ≤ 1/4) (sq_nonneg (δ*A*f))
  have hs := radial_norm_gain had (δ*A*f)
  have hroot : (Real.sqrt (1+δ^2*c^2/16))^2 = 1+δ^2*c^2/16 :=
    Real.sq_sqrt (by positivity)
  have hsq : (Real.sqrt (1+δ^2*c^2/16)*‖a‖)^2 ≤ ‖a+(δ*A*f) • r‖^2 := by
    rw [mul_pow,hroot]
    nlinarith only [hp,hs]
  have hnorm := (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt (1+δ^2*c^2/16)*‖a‖)
    (norm_nonneg (a+(δ*A*f) • r))).mp hsq
  have htri : ‖a+(δ*A*f) • r‖ ≤ ‖a+(δ*A*f) • r+e‖+‖e‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (a+(δ*A*f) • r+e) e
  linarith


end

section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open scoped InnerProductSpace
variable {X E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radial_gradient_uniform (a r : X → E) (e : ℕ → X → E)
    (q : ℕ → X → ℝ) (A f : X → ℝ) (core : Set X)
    (δ c m C : ℝ) (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hm : 0 < m)
    (ha : ∀ x, m ≤ ‖a x‖) (had : ∀ x, inner ℝ (a x) (r x) = 0)
    (herror : ∀ᶠ N : ℕ in atTop, ∀ x, ‖e N x‖ ≤ C/(N:ℝ))
    (hA : ∀ x ∈ core, ‖a x‖/2 ≤ A x)
    (hf : ∀ x ∈ core, c ≤ f x) (hr : ∀ x ∈ core, (1:ℝ)/2 ≤ ‖r x‖)
    (hq : ∀ N x, x ∈ core → q N x = δ*A x*f x)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ x,
      a x+q N x • r x+e N x ≠ 0 ∧
      (1-ε)*‖a x‖ ≤ ‖a x+q N x • r x+e N x‖ ∧
      (x ∈ core → (Real.sqrt (1+δ^2*c^2/16)-ε)*‖a x‖ ≤
        ‖a x+q N x • r x+e N x‖) := by
  have hn : Tendsto (fun N : ℕ => C/(N:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,Function.comp_apply,mul_zero] using tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have hb := hn.eventually (Iio_mem_nhds (mul_pos hε hm))
  filter_upwards [herror,hb] with N hN hC x
  have he : ‖e N x‖ ≤ ε*‖a x‖ :=
    (hN x).trans (hC.le.trans (mul_le_mul_of_nonneg_left (ha x) hε.le))
  have hl := radial_gradient_no_loss (a x) (r x) (e N x) (had x) (q N x) ε he
  refine ⟨?_,hl,?_⟩
  · apply norm_pos_iff.mp
    exact lt_of_lt_of_le (mul_pos (sub_pos.mpr hε1) (hm.trans_le (ha x))) hl
  · intro hx
    rw [hq N x hx]
    exact radial_gradient_annular_gain (a x) (r x) (e N x) (had x) δ (A x) (f x) c ε
      hδ hc (hf x hx) (hA x hx) (hr x hx) he

end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma profileTrace_add (H B : ProfileForm E) (a v : E) :
    profileTrace (H+B) a v = profileTrace H a v+profileTrace B a v := by
  simp only [profileTrace, add_apply]
  ring

omit [FiniteDimensional ℝ E] in
lemma profileTrace_smul (H : ProfileForm E) (c : ℝ) (a v : E) :
    profileTrace (c • H) a v = c*profileTrace H a v := by
  simp only [profileTrace, smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
lemma profileTrace_eq_scaled (H : ProfileForm E) (a v : E) (L : ℝ)
    (hL : L^2 = 1+‖a‖^2) :
    profileTrace H a v = H a a+H (L • v) (L • v) := by
  simp only [profileTrace, map_smul, smul_apply, smul_eq_mul]
  rw [←hL]
  ring

theorem radial_leading_profileTrace (hd : 3 ≤ Module.finrank ℝ E)
    (a r e : E) (ha : a ≠ 0) (q : ℝ) (R T : E →L[ℝ] ℝ)
    (hr : ∀ v, inner ℝ r v = R v) (hRa : R a = 0) (hTa : T a = 0)
    (he : ‖e‖ ≤ ‖a‖/2) (hrn : ‖r‖ ≤ 2)
    (hco : ∀ v, inner ℝ a v = 0 → ‖v‖/2 ≤ Real.sqrt ((R v)^2+(T v)^2))
    (A δ f b K S f₂ : ℝ) (hA : 0 ≤ A)
    (hAL : A ≤ 3*Real.sqrt (1+‖a+q • r+e‖^2))
    (hδ : 0 ≤ δ) (hf : 0 ≤ f) (hb : 0 ≤ b) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (h₂ : |f₂| ≤ K) (hq : 0 ≤ q) (hqA : q ≤ δ*A*f)
    (hfS : f^2 ≤ S*b) (hsmall : 9216*K*S*δ^2 ≤ 1)
    (B : ProfileForm E) (hB : ∀ u v, B u v = f₂*R u*R v+b*T u*T v) :
    ∃ v : E, ‖v‖ = 1 ∧ inner ℝ (a+q • r+e) v = 0 ∧
      (1+‖a+q • r+e‖^2)/32*b-8*K*‖e‖^2 ≤
        profileTrace B (a+q • r+e) v := by
  let aN := a+q • r+e
  let L := Real.sqrt (1+‖aN‖^2)
  have hLp : 0 < L := Real.sqrt_pos.mpr (by positivity)
  have hLsq : L^2 = 1+‖aN‖^2 := Real.sq_sqrt (by positivity)
  obtain ⟨w,hw,haw,hRw,htrace⟩ := radial_leading_trace hd a r e ha q R T hr hRa hTa
    he hrn hco L A δ f b K f₂ hLp.le hA hAL hδ hf hb hK h₂ hq hqA
  have ht : L^2/32*b-8*K*‖e‖^2 ≤ B aN aN+B w w := by
    have hh := radial_trace_absorption L b K S δ f ‖e‖
      (f₂*(R aN)^2+b*(T aN)^2+f₂*(R w)^2+b*(T w)^2)
      hb hK hS hfS hsmall htrace
    convert hh using 1
    rw [hB,hB]
    dsimp [aN]
    ring
  let v : E := L⁻¹ • w
  have hscaled : L • v = w := by simp [v, smul_smul, ne_of_gt hLp]
  refine ⟨v,?_,?_,?_⟩
  · simp [v,norm_smul,Real.norm_eq_abs,abs_of_pos hLp,hw,ne_of_gt hLp]
  · simp [v,inner_smul_right,haw]
  · have heq : profileTrace B aN v = B aN aN+B w w := by
      rw [profileTrace_eq_scaled B aN v L hLsq,hscaled]
    change (1+‖aN‖^2)/32*b-8*K*‖e‖^2 ≤ _
    rw [heq,←hLsq]
    exact ht

theorem radial_total_trace_lower (hd : 3 ≤ Module.finrank ℝ E)
    (a r e : E) (ha : a ≠ 0) (q : ℝ) (R T : E →L[ℝ] ℝ)
    (hr : ∀ v, inner ℝ r v = R v) (hRa : R a = 0) (hTa : T a = 0)
    (he : ‖e‖ ≤ ‖a‖/2) (hrn : ‖r‖ ≤ 2)
    (hco : ∀ v, inner ℝ a v = 0 → ‖v‖/2 ≤ Real.sqrt ((R v)^2+(T v)^2))
    (A δ f b K S f₂ : ℝ) (hA : 0 ≤ A)
    (hAL : A ≤ 3*Real.sqrt (1+‖a+q • r+e‖^2))
    (hδ : 0 ≤ δ) (hf : 0 ≤ f) (hb : 0 ≤ b) (hK : 0 ≤ K) (hS : 0 ≤ S)
    (h₂ : |f₂| ≤ K) (hq : 0 ≤ q) (hqA : q ≤ δ*A*f)
    (hfS : f^2 ≤ S*b) (hsmall : 9216*K*S*δ^2 ≤ 1)
    (B H Er : ProfileForm E) (hB : ∀ u v, B u v = f₂*R u*R v+b*T u*T v)
    (m α Hmax Gmax c : ℝ) (hm : m ≤ 1) (hα : 0 < α) (ha0 : α ≤ ‖a‖)
    (hH : ‖H‖ ≤ Hmax) (hGa : ‖a‖ ≤ Gmax) (hGN : ‖a+q • r+e‖ ≤ Gmax)
    (hc : 0 ≤ c)
    (hmargin : ∀ w, ‖w‖ = 1 → inner ℝ a w = 0 → m ≤ profileTrace H a w) :
    ∃ v : E, ‖v‖ = 1 ∧ inner ℝ (a+q • r+e) v = 0 ∧
      m-(4*Hmax*Gmax+4*Hmax*(1+Gmax^2)/α+2*(1+Hmax*(1+2*Gmax^2))/α)*
         ‖q • r+e‖ - ‖Er‖*(1+2*Gmax^2) +
        c*((1+‖a+q • r+e‖^2)/32*b-8*K*‖e‖^2) ≤
      profileTrace (H+c • B+Er) (a+q • r+e) v := by
  obtain ⟨v,hv,hav,ht⟩ := radial_leading_profileTrace hd a r e ha q R T hr hRa hTa he hrn hco
    A δ f b K S f₂ hA hAL hδ hf hb hK hS h₂ hq hqA hfS hsmall B hB
  have hbase := profileTrace_base_lower H a (a+q • r+e) v m α Hmax Gmax
    hm hα ha0 hH hGa hGN hv hav hmargin
  have hd : a+q • r+e-a = q • r+e := by abel
  rw [hd] at hbase
  have herror := profileTrace_abs_bound Er (a+q • r+e) v Gmax hGN hv
  have helo := neg_abs_le (profileTrace Er (a+q • r+e) v)
  have hscaled := mul_le_mul_of_nonneg_left ht hc
  refine ⟨v,hv,hav,?_⟩
  rw [profileTrace_add,profileTrace_add,profileTrace_smul]
  linarith

omit [FiniteDimensional ℝ E] in

lemma radial_gradient_patch_bounds (a r e : E) (δ A χ f M F C N : ℝ)
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hf : 0 ≤ f) (hfF : f ≤ F) (hr : ‖r‖ ≤ 2) (ha : ‖a‖ ≤ M)
    (hC : 0 ≤ C) (hN : 1 ≤ N) (he : ‖e‖ ≤ C/N) :
    ‖a+(δ*A*χ*f) • r+e‖ ≤ M+2*δ*A*F+C ∧
      ‖(δ*A*χ*f) • r+e‖ ≤ (2*δ*A+C)*(χ*f+N⁻¹) := by
  have hN0 : 0 < N := by linarith
  have hqn : 0 ≤ δ*A*χ*f := by positivity
  have hq : δ*A*χ*f ≤ δ*A*F := by
    calc
      _ ≤ δ*A*1*f := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hχ1 (mul_nonneg hδ hA)) hf
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hfF (mul_nonneg hδ hA)
  have hnr : ‖(δ*A*χ*f) • r‖ ≤ 2*δ*A*χ*f := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hqn]
    nlinarith only [mul_le_mul_of_nonneg_left hr hqn]
  have hnrr : ‖(δ*A*χ*f) • r‖ ≤ 2*δ*A*F := by nlinarith only [hnr,hq]
  have hen : ‖e‖ ≤ C := he.trans ((div_le_iff₀ hN0).mpr (by nlinarith))
  constructor
  · exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
      (by linarith [ha,hnrr,hen]))
  · have hh := norm_add_le ((δ*A*χ*f) • r) e
    have h1 := mul_nonneg hC (mul_nonneg hχ hf)
    have h2 := mul_nonneg (show 0 ≤ 2*δ*A by positivity) (inv_nonneg.mpr hN0.le)
    rw [div_eq_mul_inv] at he
    nlinarith only [hh,hnr,he,h1,h2]

lemma radial_scaled_leading_lower (N δ A χ f b K e C R L₂ : ℝ)
    (hN : 0 < N) (hδ : 0 ≤ δ) (hA : 0 ≤ A)
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (hf : 0 ≤ f) (hb : f/R ≤ b)
    (hK : 0 ≤ K) (he0 : 0 ≤ e) (he : e ≤ C/N) (hR : 0 < R) (hL : 1 ≤ L₂) :
    (δ*A/(32*R))*N*(χ*f)-(8*K*δ*A*C^2)/N ≤
      N*δ*A*χ*(L₂/32*b-8*K*e^2) := by
  have hb0 : 0 ≤ b := (div_nonneg hf hR.le).trans hb
  have hcoeff : 0 ≤ N*δ*A*χ := by positivity
  have hpos : (δ*A/(32*R))*N*(χ*f) ≤ N*δ*A*χ*(L₂/32*b) := by
    calc
      _ = (N*δ*A*χ)*(f/R/32) := by ring
      _ ≤ (N*δ*A*χ)*(b/32) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hb (by norm_num)) hcoeff
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) hcoeff
  have he2 : e^2 ≤ (C/N)^2 := (sq_le_sq₀ he0 (he0.trans he)).mpr he
  have herr : N*δ*A*χ*(8*K*e^2) ≤ (8*K*δ*A*C^2)/N := by
    calc
      _ ≤ N*δ*A*χ*(8*K*(C/N)^2) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left he2 (by positivity)) hcoeff
      _ ≤ N*δ*A*1*(8*K*(C/N)^2) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hχ1 (by positivity)) (by positivity)
      _ = _ := by field_simp
  nlinarith only [hpos,herr]

lemma radial_trace_collect_errors (m Cb Cg Cr Lr Clead C k N t d re lead τ : ℝ)
    (hN : 0 < N) (ht : 0 ≤ t) (hCb : 0 ≤ Cb) (hLr : 0 ≤ Lr)
    (h1 : Cb*Cg+Cr*Lr ≤ C) (h2 : Cr*Lr ≤ C)
    (h3 : Cb*Cg+Cr*Lr+Clead ≤ C)
    (hd : d ≤ Cg*(t+N⁻¹)) (hr : re ≤ Cr*(t+Real.sqrt t+N⁻¹))
    (hlead : k*N*t-Clead/N ≤ lead)
    (htrace : m-Cb*d-re*Lr+lead ≤ τ) :
    m-C*t-C*Real.sqrt t-C/N+k*N*t ≤ τ := by
  have hd' := mul_le_mul_of_nonneg_left hd hCb
  have hr' := mul_le_mul_of_nonneg_right hr hLr
  have htC := mul_le_mul_of_nonneg_right h1 ht
  have hsC := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg t)
  have heC := mul_le_mul_of_nonneg_right h3 (inv_nonneg.mpr hN.le)
  rw [div_eq_mul_inv] at hlead ⊢
  nlinarith only [htrace,hlead,hd',hr',htC,hsC,heC]

theorem radial_uniform_strict {X : Type*} (hd : 3 ≤ Module.finrank ℝ E)
    (a : X → E) (H : X → ProfileForm E) (χ : X → ℝ)
    (r e : ℕ → X → E) (R T : ℕ → X → E →L[ℝ] ℝ)
    (f b f₂ : ℕ → X → ℝ) (B Er : ℕ → X → ProfileForm E)
    (m α M Hmax δ A K S R₀ Fmax Ce Cr : ℝ)
    (hm : 0 < m) (hm1 : m ≤ 1) (hα : 0 < α) (hM : 0 ≤ M) (hHmax : 0 ≤ Hmax)
    (hδ : 0 < δ) (hA : 0 < A) (hK : 0 ≤ K) (hS : 0 ≤ S) (hR₀ : 0 < R₀)
    (hFmax : 0 ≤ Fmax) (hCe : 0 ≤ Ce) (hCr : 0 ≤ Cr)
    (hsmall : 9216*K*S*δ^2 ≤ 1)
    (ha0 : ∀ x, α ≤ ‖a x‖) (haM : ∀ x, ‖a x‖ ≤ M)
    (hHH : ∀ x, ‖H x‖ ≤ Hmax) (hAa : ∀ x, A ≤ 2*‖a x‖)
    (hmargin : ∀ x w, ‖w‖ = 1 → inner ℝ (a x) w = 0 → m ≤ profileTrace (H x) (a x) w)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hf : ∀ N x, 0 ≤ f N x ∧ f N x ≤ Fmax)
    (hb : ∀ N x, f N x/R₀ ≤ b N x) (hfS : ∀ N x, (f N x)^2 ≤ S*b N x)
    (hf₂ : ∀ N x, |f₂ N x| ≤ K)
    (hr : ∀ N x v, inner ℝ (r N x) v = R N x v)
    (hRa : ∀ N x, R N x (a x) = 0) (hTa : ∀ N x, T N x (a x) = 0)
    (hrn : ∀ N x, ‖r N x‖ ≤ 2)
    (hco : ∀ N x v, inner ℝ (a x) v = 0 →
      ‖v‖/2 ≤ Real.sqrt ((R N x v)^2+(T N x v)^2))
    (hB : ∀ N x u v, B N x u v = f₂ N x*R N x u*R N x v+b N x*T N x u*T N x v)
    (he : ∀ᶠ N : ℕ in atTop, ∀ x, ‖e N x‖ ≤ Ce/(N:ℝ))
    (hEr : ∀ᶠ N : ℕ in atTop, ∀ x, ‖Er N x‖ ≤
      Cr*(χ x*f N x+Real.sqrt (χ x*f N x)+(N:ℝ)⁻¹)) :
    ∀ᶠ N : ℕ in atTop, ∀ x,
      profileStrict (H x+((N:ℝ)*δ*A*χ x) • B N x+Er N x)
        (a x+(δ*A*χ x*f N x) • r N x+e N x) ∧
      a x+(δ*A*χ x*f N x) • r N x+e N x ≠ 0 := by
  let G := M+2*δ*A*Fmax+Ce
  let Cg := 2*δ*A+Ce
  let Cb := 4*Hmax*G+4*Hmax*(1+G^2)/α+2*(1+Hmax*(1+2*G^2))/α
  let Lr := 1+2*G^2
  let Clead := 8*K*δ*A*Ce^2
  let C := 1+Cb*Cg+Cr*Lr+Clead
  let k := δ*A/(32*R₀)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hMG : M ≤ G := by dsimp [G]; linarith only [mul_nonneg (show 0 ≤ 2*δ*A by positivity) hFmax, hCe]
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have hCb : 0 ≤ Cb := by dsimp [Cb]; positivity
  have hLr : 0 ≤ Lr := by dsimp [Lr]; positivity
  have hClead : 0 ≤ Clead := by dsimp [Clead]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hCCg : Cb*Cg+Cr*Lr ≤ C := by dsimp [C]; linarith only [hClead]
  have hCCr : Cr*Lr ≤ C := by dsimp [C]; linarith only [mul_nonneg hCb hCg,hClead]
  have hCCe : Cb*Cg+Cr*Lr+Clead ≤ C := by dsimp [C]; linarith only [hClead]
  have hnat : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv (c : ℝ) : Tendsto (fun N : ℕ => c/(N:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,Function.comp_apply,mul_zero] using
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hnat)
  have hNone : ∀ᶠ N : ℕ in atTop, (1:ℝ) ≤ (N:ℝ) := hnat.eventually (eventually_ge_atTop _)
  have heSmall := (hinv Ce).eventually (Iio_mem_nhds (by positivity : (0:ℝ) < α/3))
  have hη := (hinv C).eventually (Iio_mem_nhds (by positivity : (0:ℝ) < m/4))
  have hlarge : ∀ᶠ N : ℕ in atTop, (C+C^2/m)/k ≤ (N:ℝ) :=
    hnat.eventually (eventually_ge_atTop _)
  filter_upwards [he,hEr,hNone,heSmall,hη,hlarge] with N heN hErN hN1 heS hηN hLN x
  have hN : 0 < (N:ℝ) := lt_of_lt_of_le zero_lt_one hN1
  let q := δ*A*χ x*f N x
  let aN := a x+q • r N x+e N x
  let t := χ x*f N x
  have ht : 0 ≤ t := mul_nonneg (hχ x).1 (hf N x).1
  have hqn : 0 ≤ q := mul_nonneg (mul_nonneg (mul_nonneg hδ.le hA.le) (hχ x).1) (hf N x).1
  have hqA : q ≤ δ*A*f N x := by
    dsimp [q]
    simpa using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hχ x).2 (mul_nonneg hδ.le hA.le)) (hf N x).1
  have haNe : a x ≠ 0 := norm_pos_iff.mp (hα.trans_le (ha0 x))
  have hethird : ‖e N x‖ ≤ ‖a x‖/3 := (heN x).trans
    (heS.le.trans (div_le_div_of_nonneg_right (ha0 x) (by norm_num)))
  have hehalf : ‖e N x‖ ≤ ‖a x‖/2 := by linarith only [hethird,norm_nonneg (a x)]
  have had : inner ℝ (a x) (r N x) = 0 := by rw [real_inner_comm,hr,hRa]
  have hnl : (1-(1/3:ℝ))*‖a x‖ ≤ ‖aN‖ :=
    radial_gradient_no_loss (a x) (r N x) (e N x) had q (1/3) (by linarith only [hethird])
  have haNNe : aN ≠ 0 := norm_pos_iff.mp (by nlinarith only [ha0 x,hnl,hα])
  have hL : ‖aN‖ ≤ Real.sqrt (1+‖aN‖^2) := by
    nlinarith only [Real.sq_sqrt (show 0 ≤ 1+‖aN‖^2 by positivity),
      Real.sqrt_nonneg (1+‖aN‖^2),norm_nonneg aN]
  have hAL : A ≤ 3*Real.sqrt (1+‖aN‖^2) := by linarith only [hAa x,hnl,hL]
  obtain ⟨haNG,hdiff⟩ := radial_gradient_patch_bounds (a x) (r N x) (e N x)
    δ A (χ x) (f N x) M Fmax Ce (N:ℝ) hδ.le hA.le (hχ x).1 (hχ x).2
    (hf N x).1 (hf N x).2 (hrn N x) (haM x) hCe hN1 (heN x)
  have hb0 : 0 ≤ b N x := (div_nonneg (hf N x).1 hR₀.le).trans (hb N x)
  obtain ⟨v,hv,hav,htrace⟩ := radial_total_trace_lower hd (a x) (r N x) (e N x) haNe q
    (R N x) (T N x) (hr N x) (hRa N x) (hTa N x) hehalf (hrn N x) (hco N x)
    A δ (f N x) (b N x) K S (f₂ N x) hA.le hAL hδ.le (hf N x).1 hb0 hK hS
    (hf₂ N x) hqn hqA (hfS N x) hsmall (B N x) (H x) (Er N x) (hB N x)
    m α Hmax G ((N:ℝ)*δ*A*χ x) hm1 hα (ha0 x) (hHH x) ((haM x).trans hMG)
    haNG (mul_nonneg (mul_nonneg (mul_nonneg hN.le hδ.le) hA.le) (hχ x).1) (hmargin x)
  have hscaled := radial_scaled_leading_lower (N:ℝ) δ A (χ x) (f N x) (b N x) K
    ‖e N x‖ Ce R₀ (1+‖aN‖^2) hN hδ.le hA.le (hχ x).1 (hχ x).2
    (hf N x).1 (hb N x) hK (norm_nonneg _) (heN x) hR₀ (by linarith only [sq_nonneg ‖aN‖])
  have hτ := radial_trace_collect_errors m Cb Cg Cr Lr Clead C k (N:ℝ) t
    ‖q • r N x+e N x‖ ‖Er N x‖
    ((N:ℝ)*δ*A*χ x*((1+‖aN‖^2)/32*b N x-8*K*‖e N x‖^2))
    (profileTrace (H x+((N:ℝ)*δ*A*χ x) • B N x+Er N x) aN v)
    hN ht hCb hLr hCCg hCCr hCCe hdiff (hErN x) hscaled htrace
  have hD : C^2 ≤ (k*(N:ℝ)-C)*m := by
    have hh := (div_le_iff₀ hk).mp hLN
    apply (div_le_iff₀ hm).mp
    nlinarith only [hh]
  have hpos := radial_transition_positive m C (k*(N:ℝ)) t (C/(N:ℝ))
    (profileTrace (H x+((N:ℝ)*δ*A*χ x) • B N x+Er N x) aN v)
    hm ht hηN.le hD hτ
  exact ⟨⟨v,hv,hav,lt_of_lt_of_le (by positivity) hpos⟩,haNNe⟩

theorem radial_uniform_strict_bundle {X : Type*} {V : X → Type*}
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [∀ x, FiniteDimensional ℝ (V x)] (hd : ∀ x, 3 ≤ Module.finrank ℝ (V x))
    (a : ∀ x, V x) (H : ∀ x, ProfileForm (V x)) (χ : X → ℝ)
    (r e : ℕ → ∀ x, V x) (R T : ℕ → ∀ x, V x →L[ℝ] ℝ)
    (f b f₂ : ℕ → X → ℝ) (B Er : ℕ → ∀ x, ProfileForm (V x))
    (m α M Hmax δ A K S R₀ Fmax Ce Cr : ℝ)
    (hm : 0 < m) (hm1 : m ≤ 1) (hα : 0 < α) (hM : 0 ≤ M) (hHmax : 0 ≤ Hmax)
    (hδ : 0 < δ) (hA : 0 < A) (hK : 0 ≤ K) (hS : 0 ≤ S) (hR₀ : 0 < R₀)
    (hFmax : 0 ≤ Fmax) (hCe : 0 ≤ Ce) (hCr : 0 ≤ Cr)
    (hsmall : 9216*K*S*δ^2 ≤ 1)
    (ha0 : ∀ x, α ≤ ‖a x‖) (haM : ∀ x, ‖a x‖ ≤ M)
    (hHH : ∀ x, ‖H x‖ ≤ Hmax) (hAa : ∀ x, A ≤ 2*‖a x‖)
    (hmargin : ∀ x w, ‖w‖ = 1 → inner ℝ (a x) w = 0 → m ≤ profileTrace (H x) (a x) w)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hf : ∀ N x, 0 ≤ f N x ∧ f N x ≤ Fmax)
    (hb : ∀ N x, f N x/R₀ ≤ b N x) (hfS : ∀ N x, (f N x)^2 ≤ S*b N x)
    (hf₂ : ∀ N x, |f₂ N x| ≤ K)
    (hr : ∀ N x v, inner ℝ (r N x) v = R N x v)
    (hRa : ∀ N x, R N x (a x) = 0) (hTa : ∀ N x, T N x (a x) = 0)
    (hrn : ∀ N x, ‖r N x‖ ≤ 2)
    (hco : ∀ N x v, inner ℝ (a x) v = 0 →
      ‖v‖/2 ≤ Real.sqrt ((R N x v)^2+(T N x v)^2))
    (hB : ∀ N x u v, B N x u v = f₂ N x*R N x u*R N x v+b N x*T N x u*T N x v)
    (he : ∀ᶠ N : ℕ in atTop, ∀ x, ‖e N x‖ ≤ Ce/(N:ℝ))
    (hEr : ∀ᶠ N : ℕ in atTop, ∀ x, ‖Er N x‖ ≤
      Cr*(χ x*f N x+Real.sqrt (χ x*f N x)+(N:ℝ)⁻¹)) :
    ∀ᶠ N : ℕ in atTop, ∀ x,
      profileStrict (H x+((N:ℝ)*δ*A*χ x) • B N x+Er N x)
        (a x+(δ*A*χ x*f N x) • r N x+e N x) ∧
      a x+(δ*A*χ x*f N x) • r N x+e N x ≠ 0 := by
  let G := M+2*δ*A*Fmax+Ce
  let Cg := 2*δ*A+Ce
  let Cb := 4*Hmax*G+4*Hmax*(1+G^2)/α+2*(1+Hmax*(1+2*G^2))/α
  let Lr := 1+2*G^2
  let Clead := 8*K*δ*A*Ce^2
  let C := 1+Cb*Cg+Cr*Lr+Clead
  let k := δ*A/(32*R₀)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hMG : M ≤ G := by dsimp [G]; linarith only [mul_nonneg (show 0 ≤ 2*δ*A by positivity) hFmax, hCe]
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  have hCb : 0 ≤ Cb := by dsimp [Cb]; positivity
  have hLr : 0 ≤ Lr := by dsimp [Lr]; positivity
  have hClead : 0 ≤ Clead := by dsimp [Clead]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hCCg : Cb*Cg+Cr*Lr ≤ C := by dsimp [C]; linarith only [hClead]
  have hCCr : Cr*Lr ≤ C := by dsimp [C]; linarith only [mul_nonneg hCb hCg,hClead]
  have hCCe : Cb*Cg+Cr*Lr+Clead ≤ C := by dsimp [C]; linarith only [hClead]
  have hnat : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv (c : ℝ) : Tendsto (fun N : ℕ => c/(N:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,Function.comp_apply,mul_zero] using
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hnat)
  have hNone : ∀ᶠ N : ℕ in atTop, (1:ℝ) ≤ (N:ℝ) := hnat.eventually (eventually_ge_atTop _)
  have heSmall := (hinv Ce).eventually (Iio_mem_nhds (by positivity : (0:ℝ) < α/3))
  have hη := (hinv C).eventually (Iio_mem_nhds (by positivity : (0:ℝ) < m/4))
  have hlarge : ∀ᶠ N : ℕ in atTop, (C+C^2/m)/k ≤ (N:ℝ) :=
    hnat.eventually (eventually_ge_atTop _)
  filter_upwards [he,hEr,hNone,heSmall,hη,hlarge] with N heN hErN hN1 heS hηN hLN x
  have hN : 0 < (N:ℝ) := lt_of_lt_of_le zero_lt_one hN1
  let q := δ*A*χ x*f N x
  let aN := a x+q • r N x+e N x
  let t := χ x*f N x
  have ht : 0 ≤ t := mul_nonneg (hχ x).1 (hf N x).1
  have hqn : 0 ≤ q := mul_nonneg (mul_nonneg (mul_nonneg hδ.le hA.le) (hχ x).1) (hf N x).1
  have hqA : q ≤ δ*A*f N x := by
    dsimp [q]
    simpa using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hχ x).2 (mul_nonneg hδ.le hA.le)) (hf N x).1
  have haNe : a x ≠ 0 := norm_pos_iff.mp (hα.trans_le (ha0 x))
  have hethird : ‖e N x‖ ≤ ‖a x‖/3 := (heN x).trans
    (heS.le.trans (div_le_div_of_nonneg_right (ha0 x) (by norm_num)))
  have hehalf : ‖e N x‖ ≤ ‖a x‖/2 := by linarith only [hethird,norm_nonneg (a x)]
  have had : inner ℝ (a x) (r N x) = 0 := by rw [real_inner_comm,hr,hRa]
  have hnl : (1-(1/3:ℝ))*‖a x‖ ≤ ‖aN‖ :=
    radial_gradient_no_loss (a x) (r N x) (e N x) had q (1/3) (by linarith only [hethird])
  have haNNe : aN ≠ 0 := norm_pos_iff.mp (by nlinarith only [ha0 x,hnl,hα])
  have hL : ‖aN‖ ≤ Real.sqrt (1+‖aN‖^2) := by
    nlinarith only [Real.sq_sqrt (show 0 ≤ 1+‖aN‖^2 by positivity),
      Real.sqrt_nonneg (1+‖aN‖^2),norm_nonneg aN]
  have hAL : A ≤ 3*Real.sqrt (1+‖aN‖^2) := by linarith only [hAa x,hnl,hL]
  obtain ⟨haNG,hdiff⟩ := radial_gradient_patch_bounds (a x) (r N x) (e N x)
    δ A (χ x) (f N x) M Fmax Ce (N:ℝ) hδ.le hA.le (hχ x).1 (hχ x).2
    (hf N x).1 (hf N x).2 (hrn N x) (haM x) hCe hN1 (heN x)
  have hb0 : 0 ≤ b N x := (div_nonneg (hf N x).1 hR₀.le).trans (hb N x)
  obtain ⟨v,hv,hav,htrace⟩ := radial_total_trace_lower (hd x) (a x) (r N x) (e N x) haNe q
    (R N x) (T N x) (hr N x) (hRa N x) (hTa N x) hehalf (hrn N x) (hco N x)
    A δ (f N x) (b N x) K S (f₂ N x) hA.le hAL hδ.le (hf N x).1 hb0 hK hS
    (hf₂ N x) hqn hqA (hfS N x) hsmall (B N x) (H x) (Er N x) (hB N x)
    m α Hmax G ((N:ℝ)*δ*A*χ x) hm1 hα (ha0 x) (hHH x) ((haM x).trans hMG)
    haNG (mul_nonneg (mul_nonneg (mul_nonneg hN.le hδ.le) hA.le) (hχ x).1) (hmargin x)
  have hscaled := radial_scaled_leading_lower (N:ℝ) δ A (χ x) (f N x) (b N x) K
    ‖e N x‖ Ce R₀ (1+‖aN‖^2) hN hδ.le hA.le (hχ x).1 (hχ x).2
    (hf N x).1 (hb N x) hK (norm_nonneg _) (heN x) hR₀ (by linarith only [sq_nonneg ‖aN‖])
  have hτ := radial_trace_collect_errors m Cb Cg Cr Lr Clead C k (N:ℝ) t
    ‖q • r N x+e N x‖ ‖Er N x‖
    ((N:ℝ)*δ*A*χ x*((1+‖aN‖^2)/32*b N x-8*K*‖e N x‖^2))
    (profileTrace (H x+((N:ℝ)*δ*A*χ x) • B N x+Er N x) aN v)
    hN ht hCb hLr hCCg hCCr hCCe hdiff (hErN x) hscaled htrace
  have hD : C^2 ≤ (k*(N:ℝ)-C)*m := by
    have hh := (div_le_iff₀ hk).mp hLN
    apply (div_le_iff₀ hm).mp
    nlinarith only [hh]
  have hpos := radial_transition_positive m C (k*(N:ℝ)) t (C/(N:ℝ))
    (profileTrace (H x+((N:ℝ)*δ*A*χ x) • B N x+Er N x) aN v)
    hm ht hηN.le hD hτ
  exact ⟨⟨v,hv,hav,lt_of_lt_of_le (by positivity) hpos⟩,haNNe⟩



end YauCounterexamples
end

end OAI
