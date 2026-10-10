import OAI.NumberTheory.DirichletL.PrincipalMellinResidues
import OAI.NumberTheory.DirichletL.ContinuationPolynomialContour
import Mathlib.MeasureTheory.Group.Prod

namespace OAI

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology
namespace SevenEighths.ProbeMellinBoundary
open PrincipalMellinResidues HeckeFamily EisensteinSchwartzPoisson

def height (t : ℝ) : ℝ := 1+|t|
lemma height_pos (t : ℝ) : 0<height t := by unfold height; positivity
lemma height_one_le (t : ℝ) : 1≤height t := by simp [height]

def cauchy (t : ℝ) : ℝ := (1+t^2)⁻¹
lemma cauchy_nonneg (t : ℝ) : 0≤cauchy t := by unfold cauchy; positivity
lemma cauchy_integrable : Integrable cauchy := integrable_inv_one_add_sq
lemma cauchy_tendsto : Tendsto cauchy atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_left atTop (1:ℝ) (tendsto_pow_atTop (by decide : 2≠0)))

theorem boundaryControl_of_cauchy (F : ℂ → ℂ) {a b C : ℝ}
    (ha : Continuous (fun t : ℝ => F ((a:ℂ)+t*I)))
    (hb : Continuous (fun t : ℝ => F ((b:ℂ)+t*I)))
    (hla : ∀t : ℝ, ‖F ((a:ℂ)+t*I)‖≤C*cauchy t)
    (hlb : ∀t : ℝ, ‖F ((b:ℂ)+t*I)‖≤C*cauchy t)
    (hjoin : ∀x∈uIcc a b, ∀t : ℝ, 1≤|t| → ‖F ((x:ℂ)+t*I)‖≤C*cauchy t) :
    BoundaryControl F a b := by
  have hi (h : Continuous (fun t : ℝ => F ((a:ℂ)+t*I))) :=
    (cauchy_integrable.const_mul C).mono' h.aestronglyMeasurable (Eventually.of_forall hla)
  have hj (ε : ℝ) (hε : |ε|=1) :
      Tendsto (fun T : ℝ => ∫x : ℝ in a..b, F ((x:ℂ)+(ε*T)*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
      (by simpa using (cauchy_tendsto.const_mul C).mul_const |b-a|)
    filter_upwards [eventually_ge_atTop 1] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have ht : |ε*T|=T := by rw [abs_mul,hε,one_mul,abs_of_nonneg (by linarith)]
    have hh := hjoin x (uIoc_subset_uIcc hx) (ε*T) (by simpa [ht] using hT)
    have he : cauchy (ε*T)=cauchy T := by
      unfold cauchy
      have hs : (ε*T)^2=T^2 := by nlinarith [sq_abs (ε*T)]
      rw [hs]
    simpa [he] using hh
  refine ⟨hi ha, (cauchy_integrable.const_mul C).mono' hb.aestronglyMeasurable
    (Eventually.of_forall hlb), ?_, ?_⟩
  · simpa using hj (-1) (by norm_num)
  · simpa using hj 1 (by norm_num)

lemma pole_distance_vertical (p x t : ℝ) : |x-p|≤‖(x:ℂ)+t*I-p‖ := by
  simpa using Complex.abs_re_le_norm ((x:ℂ)+t*I-p)
lemma pole_distance_horizontal (p x t : ℝ) : |t|≤‖(x:ℂ)+t*I-p‖ := by
  simpa using Complex.abs_im_le_norm ((x:ℂ)+t*I-p)

theorem boundaryControl_of_pole_product (F V G : ℂ → ℂ) {a b p C D δ : ℝ} (J : ℕ)
    (hδ : 0<δ) (hδ1 : δ≤1) (hpa : δ≤|a-p|) (hpb : δ≤|b-p|)
    (hF : ∀x∈uIcc a b, ∀t : ℝ, (x:ℂ)+t*I≠p →
      F ((x:ℂ)+t*I)=V ((x:ℂ)+t*I)*G ((x:ℂ)+t*I)/((x:ℂ)+t*I-p))
    (hV : ContinuousOn V {z : ℂ | z.re∈uIcc a b})
    (hG : ContinuousOn G {z : ℂ | z.re∈uIcc a b})
    (_hC : 0≤C) (hD : 0≤D)
    (hVbd : ∀x∈uIcc a b, ∀t : ℝ, height t^(J+2)*‖V ((x:ℂ)+t*I)‖≤C)
    (hGbd : ∀x∈uIcc a b, ∀t : ℝ, (x=a ∨ x=b ∨ 1≤|t|) →
      ‖G ((x:ℂ)+t*I)‖≤D*height t^J) :
    BoundaryControl F a b := by
  have hne (x t : ℝ) (hd : δ≤‖(x:ℂ)+t*I-p‖) : (x:ℂ)+t*I≠p := by
    intro h
    rw [h, sub_self, norm_zero] at hd
    linarith
  have hc (x : ℝ) (hx : x∈uIcc a b) (hd : δ≤|x-p|) :
      Continuous (fun t : ℝ => F ((x:ℂ)+t*I)) := by
    have hn (t : ℝ) : (x:ℂ)+t*I≠p := hne x t (hd.trans (pole_distance_vertical p x t))
    have hv := hV.comp_continuous (by fun_prop : Continuous (fun t : ℝ => (x:ℂ)+t*I))
      (by intro t; simpa using hx)
    have hg := hG.comp_continuous (by fun_prop : Continuous (fun t : ℝ => (x:ℂ)+t*I))
      (by intro t; simpa using hx)
    exact ((hv.mul hg).div (by fun_prop) (fun t => sub_ne_zero.mpr (hn t))).congr
      (fun t => (hF x hx t (hn t)).symm)
  have hbound (x : ℝ) (hx : x∈uIcc a b) (t : ℝ)
      (hd : δ≤‖(x:ℂ)+t*I-p‖) (hboundary : x=a ∨ x=b ∨ 1≤|t|) : ‖F ((x:ℂ)+t*I)‖≤(C*D/δ)*cauchy t := by
    have hn := hne x t hd
    have hv : height t^2 * (height t^J*‖V ((x:ℂ)+t*I)‖)≤C := by
      simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hVbd x hx t
    have hv' := CubicReflectionKernel.weighted_two_to_cauchy
      (mul_nonneg (pow_nonneg (height_pos t).le _) (norm_nonneg _)) t hv
    change height t^J*‖V ((x:ℂ)+t*I)‖≤C*cauchy t at hv'
    rw [hF x hx t hn, norm_div, norm_mul]
    apply (div_le_div₀ (mul_nonneg (norm_nonneg _) (mul_nonneg hD (pow_nonneg (height_pos t).le _)))
      (mul_le_mul_of_nonneg_left (hGbd x hx t hboundary) (norm_nonneg _)) hδ hd).trans
    calc
      ‖V ((x:ℂ)+t*I)‖*(D*height t^J)/δ = D/δ*(height t^J*‖V ((x:ℂ)+t*I)‖) := by ring
      _ ≤ D/δ*(C*cauchy t) := mul_le_mul_of_nonneg_left hv' (div_nonneg hD hδ.le)
      _ = _ := by ring
  apply boundaryControl_of_cauchy F (hc a (left_mem_uIcc) hpa) (hc b (right_mem_uIcc) hpb)
  · intro t
    exact hbound a left_mem_uIcc t (hpa.trans (pole_distance_vertical p a t)) (Or.inl rfl)
  · intro t
    exact hbound b right_mem_uIcc t (hpb.trans (pole_distance_vertical p b t)) (Or.inr (Or.inl rfl))
  · intro x hx t ht
    exact hbound x hx t ((hδ1.trans ht).trans (pole_distance_horizontal p x t)) (Or.inr (Or.inr ht))

def scaleBound (q lo hi : ℝ) : ℝ := Real.exp (max (Real.log q*lo) (Real.log q*hi))
lemma scaleBound_pos (q lo hi : ℝ) : 0<scaleBound q lo hi := Real.exp_pos _
lemma rpow_le_scaleBound {q lo hi x : ℝ} (hq : 0<q) (hx : x∈Icc lo hi) :
    q^x≤scaleBound q lo hi := by
  rw [Real.rpow_def_of_pos hq]
  apply Real.exp_le_exp.mpr
  by_cases hl : 0≤Real.log q
  · exact (mul_le_mul_of_nonneg_left hx.2 hl).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge hl)).trans (le_max_left _ _)
lemma cpow_le_scaleBound {q lo hi : ℝ} (hq : 0<q) (z : ℂ) (hz : z.re∈Icc lo hi) :
    ‖(q:ℂ)^z‖≤scaleBound q lo hi := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hq]
  exact rpow_le_scaleBound hq hz

def wScalar (W0 : SchwartzMap ℝ ℂ) (X Z : ℝ) (eta : Character) (s z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
    mellin (paperRadialFourier W0) z / LFunction eta s

theorem source_w_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ)
    (ha1 : 0<a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0<Y)
    (eta : Character) (s z : ℂ) (hEta : LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {cw AH AL : ℝ}
    (hcw : 1<cw) (hAH : 0≤AH) (hAL : 0≤AL) (JH JL : ℕ)
    (hHB : ContinuousOn (fun w => H w z*B w z) {w : ℂ | (19/20:ℝ)≤w.re ∧ w.re≤cw})
    (hHBbd : ∀x∈Icc (19/20:ℝ) cw, ∀t : ℝ, (x=19/20 ∨ x=cw ∨ 1≤|t|) →
      ‖H ((x:ℂ)+t*I) z * B ((x:ℂ)+t*I) z‖≤AH*height t^JH)
    (hLbd : ∀x∈Icc (19/20:ℝ) cw, ∀t : ℝ, (x=19/20 ∨ x=cw ∨ 1≤|t|) →
      ‖HeckeOrigin.poleRemoved (fixedPrincipal M) ((x:ℂ)+t*I)‖≤AL*height t^JL) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z eta s H B w z *
      LFunction (fixedPrincipal M) w) (19/20) cw := by
  let δ : ℝ := min (1/20) (cw-1)
  have hδ : 0<δ := lt_min (by norm_num) (sub_pos.mpr hcw)
  have hab : (19/20:ℝ)≤cw := by linarith
  have hu : uIcc (19/20:ℝ) cw=Icc (19/20:ℝ) cw := uIcc_of_le hab
  obtain ⟨C,hC,hV⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) (19/20) cw (JH+JL+2)
  let G (w : ℂ) := wScalar W0 X Z eta s z * (Y:ℂ)^(w-1) *
    (H w z*B w z) * HeckeOrigin.poleRemoved (fixedPrincipal M) w
  have hGc : ContinuousOn G {w : ℂ | w.re∈uIcc (19/20:ℝ) cw} := by
    apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · exact (continuous_const.mul ((continuous_id.sub continuous_const).const_cpow
          (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne')))).continuousOn
      · rw [hu]; exact hHB
    · exact (HeckeOrigin.poleRemoved_entire (fixedPrincipal M)).continuous.continuousOn
  apply boundaryControl_of_pole_product _ (mellin W1) G (p:=1) (δ:=δ) (C:=C)
    (D:=‖wScalar W0 X Z eta s z‖*scaleBound Y (19/20-1) (cw-1)*AH*AL) (JH+JL)
    hδ (by dsimp [δ]; exact (min_le_left _ _).trans (by norm_num))
    (by dsimp [δ]; norm_num)
    (by dsimp [δ]; rw [abs_of_pos (sub_pos.mpr hcw)]; exact min_le_right _ _) ?_
    (CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1
      (W1.smooth ⊤)).continuous.continuousOn hGc hC.le
    (by unfold scaleBound; positivity) (by intro x hx t; exact hV x (hu ▸ hx) t) ?_
  · intro x hx t hn
    have hxp := (hu ▸ hx).1
    have h0 : (x:ℂ)+t*I≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have h1 : (x:ℂ)+t*I≠1 := by simpa using hn
    dsimp only [G]
    rw [HeckeOrigin.poleRemoved_eq _ h0 h1]
    unfold sourceMultiplier wScalar
    norm_num only [Complex.ofReal_one]
    field_simp [hEta]
  · intro x hx t hboundary
    have hv := cpow_le_scaleBound hY (((x:ℂ)+t*I)-1)
      (show (((x:ℂ)+t*I)-1).re∈Icc (19/20-1) (cw-1) by
        simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,mul_zero,zero_mul,
          sub_zero,add_zero,one_re]
        exact ⟨sub_le_sub_right (hu ▸ hx).1 1, sub_le_sub_right (hu ▸ hx).2 1⟩)
    dsimp only [G]
    rw [norm_mul,norm_mul,norm_mul]
    calc
      _ ≤ ‖wScalar W0 X Z eta s z‖ * scaleBound Y (19/20-1) (cw-1) *
          (AH*height t^JH) * (AL*height t^JL) := by
        have hscale := (scaleBound_pos Y (19/20-1) (cw-1)).le
        have hp := (height_pos t).le
        exact mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
            (hHBbd x (hu ▸ hx) t hboundary) (norm_nonneg _) (by positivity))
          (hLbd x (hu ▸ hx) t hboundary) (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_add]; ring

lemma gaussian_strip_norm_le (s : ℂ) {a b x : ℝ} (ha : 0<a) (hx : x∈Icc a b) (t : ℝ) :
    ‖Complex.exp ((s+((x:ℂ)+t*I)-1)^2)‖≤Real.exp ((|s.re|+b+1)^2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hr : ((s+((x:ℂ)+t*I)-1)^2).re = (s.re+x-1)^2-(s.im+t)^2 := by simp [pow_two]
  rw [hr]
  have hxb : 0<x := ha.trans_le hx.1
  have hK : 0≤|s.re|+b+1 := by linarith [abs_nonneg s.re, hx.2]
  have hA : |s.re+x-1|≤|s.re|+b+1 := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le s.re, le_abs_self s.re, hx.2]
  have hsq := pow_le_pow_left₀ (abs_nonneg (s.re+x-1)) hA 2
  rw [sq_abs] at hsq
  nlinarith [sq_nonneg (s.im+t)]

def zScalar (W1 : SchwartzMap ℝ ℂ) (X Z : ℝ) (eta : Character) (s z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*mellin W1 1 / LFunction eta s

def zScaleBound (W1 : SchwartzMap ℝ ℂ) (X Z : ℝ) (eta : Character) (s : ℂ) (a b : ℝ) : ℝ :=
  scaleBound X (1/2-b) (1/2-a) * scaleBound Z (s.re+a-1) (s.re+b-1) *
    Real.exp ((|s.re|+b+1)^2) * ‖mellin W1 1‖ / ‖LFunction eta s‖

lemma zScalar_continuous (W1 : SchwartzMap ℝ ℂ) {X Z : ℝ} (hX : 0<X) (hZ : 0<Z)
    (eta : Character) (s : ℂ) : Continuous (zScalar W1 X Z eta s) := by
  unfold zScalar
  apply Continuous.div_const
  apply Continuous.mul_const
  apply Continuous.mul
  · exact (((continuous_const.sub continuous_id).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).mul
      (((continuous_const.add continuous_id).sub continuous_const).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))))
  · fun_prop

lemma zScalar_norm_le (W1 : SchwartzMap ℝ ℂ) {X Z a b x : ℝ}
    (hX : 0<X) (hZ : 0<Z) (ha : 0<a) (hx : x∈Icc a b)
    (eta : Character) (s : ℂ) (t : ℝ) :
    ‖zScalar W1 X Z eta s ((x:ℂ)+t*I)‖≤zScaleBound W1 X Z eta s a b := by
  unfold zScalar zScaleBound
  simp only [norm_div,norm_mul]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul
  · apply mul_le_mul
    · apply cpow_le_scaleBound hX
      simpa using And.intro (sub_le_sub_left hx.2 (1/2)) (sub_le_sub_left hx.1 (1/2))
    · apply cpow_le_scaleBound hZ
      simpa using And.intro (by linarith [hx.1] : s.re+a-1≤s.re+x-1)
        (by linarith [hx.2] : s.re+x-1≤s.re+b-1)
    · exact norm_nonneg _
    · exact (scaleBound_pos _ _ _).le
  · exact gaussian_strip_norm_le s ha hx t
  · exact norm_nonneg _
  · exact mul_nonneg (scaleBound_pos _ _ _).le (scaleBound_pos _ _ _).le

theorem source_z_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ)
    (ha0 : 0<a0) (hW0 : Function.support W0⊆Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (eta : Character) (s : ℂ) (hEta : LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {e AH AL : ℝ}
    (he : 0<e) (hAH : 0≤AH) (hAL : 0≤AL) (JH JL : ℕ)
    (hHB : ContinuousOn (fun z => H 1 z*B 1 z)
      {z : ℂ | (33/200:ℝ)≤z.re ∧ z.re≤1/6+e})
    (hHBbd : ∀x∈Icc (33/200:ℝ) (1/6+e), ∀t : ℝ, (x=33/200 ∨ x=1/6+e ∨ 1≤|t|) →
      ‖H 1 ((x:ℂ)+t*I) * B 1 ((x:ℂ)+t*I)‖≤AH*height t^JH)
    (hLbd : ∀x∈Icc (33/200:ℝ) (1/6+e), ∀t : ℝ, (x=33/200 ∨ x=1/6+e ∨ 1≤|t|) →
      ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((x:ℂ)+t*I))‖≤AL*height t^JL) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z eta s H B 1 z *
      LFunction (fixedPrincipal M) (6*z)) (33/200) (1/6+e) := by
  let δ : ℝ := min (1/600) e
  have hδ : 0<δ := lt_min (by norm_num) he
  have hab : (33/200:ℝ)≤1/6+e := by linarith
  have hu : uIcc (33/200:ℝ) (1/6+e)=Icc (33/200:ℝ) (1/6+e) := uIcc_of_le hab
  obtain ⟨C,hC,hV⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0
    (33/200) (1/6+e) (by norm_num) (JH+JL+2)
  let G (z : ℂ) := zScalar W1 X Z eta s z * (H 1 z*B 1 z) *
    HeckeOrigin.poleRemoved (fixedPrincipal M) (6*z) / 6
  have hGc : ContinuousOn G {z : ℂ | z.re∈uIcc (33/200:ℝ) (1/6+e)} := by
    apply ContinuousOn.div_const
    apply ContinuousOn.mul
    · exact (zScalar_continuous W1 hX hZ eta s).continuousOn.mul (by rw [hu]; exact hHB)
    · exact ((HeckeOrigin.poleRemoved_entire (fixedPrincipal M)).continuous.comp
        (continuous_const.mul continuous_id)).continuousOn
  apply boundaryControl_of_pole_product _ (mellin (paperRadialFourier W0)) G
    (p:=1/6) (δ:=δ) (C:=C)
    (D:=zScaleBound W1 X Z eta s (33/200) (1/6+e)*AH*AL/6) (JH+JL)
    hδ (by dsimp [δ]; exact (min_le_left _ _).trans (by norm_num))
    (by dsimp [δ]; norm_num)
    (by dsimp [δ]; rw [show (1/6+e:ℝ)-1/6=e by ring, abs_of_pos he]; exact min_le_right _ _)
    ?_ ?_ hGc hC.le (by unfold zScaleBound scaleBound; positivity) (by intro x hx t; exact hV x (hu ▸ hx) t) ?_
  · intro x hx t hn
    have hxp := (hu ▸ hx).1
    have h0 : 6*((x:ℂ)+t*I)≠0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    have h1 : 6*((x:ℂ)+t*I)≠1 := by
      intro h
      apply hn
      push_cast
      linear_combination h/6
    have hd : (x:ℂ)+t*I-(1/6:ℂ)≠0 := sub_ne_zero.mpr (by simpa using hn)
    dsimp only [G]
    rw [HeckeOrigin.poleRemoved_eq _ h0 h1]
    norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
    apply (eq_div_iff hd).mpr
    unfold sourceMultiplier zScalar
    norm_num only [sub_self,Complex.cpow_zero,mul_one]
    field_simp [hEta]
  · apply (ProbeRadialMellin.radial_mellin_differentiable W0).continuousOn.mono
    intro z hz
    have := (hu ▸ hz).1
    change 0<z.re
    linarith
  · intro x hx t hboundary
    dsimp only [G]
    rw [norm_div,norm_mul,norm_mul]
    norm_num only [Complex.norm_ofNat]
    calc
      _ ≤ (zScaleBound W1 X Z eta s (33/200) (1/6+e) *
          (AH*height t^JH) * (AL*height t^JL))/6 := by
        have hS : 0≤zScaleBound W1 X Z eta s (33/200) (1/6+e) := by
          unfold zScaleBound scaleBound
          positivity
        have hp := (height_pos t).le
        apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ)≤6)
        exact mul_le_mul
          (mul_le_mul (zScalar_norm_le W1 hX hZ (by norm_num) (hu ▸ hx) eta s t)
            (hHBbd x (hu ▸ hx) t hboundary) (norm_nonneg _) hS)
          (hLbd x (hu ▸ hx) t hboundary) (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_add]; ring

def profile (W0 W1 : SchwartzMap ℝ ℂ) (s w z : ℂ) : ℂ :=
  Complex.exp ((s+z-1)^2) * mellin (paperRadialFourier W0) z * mellin W1 w

def jointHeight (t v w : ℝ) : ℝ := 1+|t|+|v|+|w|
lemma jointHeight_pos (t v w : ℝ) : 0<jointHeight t v w := by unfold jointHeight; positivity

def gaussianMoment (n : ℕ) (u : ℝ) : ℝ := height u^n*Real.exp (-(u^2))
lemma gaussianMoment_nonneg (n : ℕ) (u : ℝ) : 0≤gaussianMoment n u := by
  unfold gaussianMoment height
  positivity
lemma gaussianMoment_integrable (n : ℕ) : Integrable (gaussianMoment n) := by
  apply ((Continuation.polynomialGaussian_integrable n).const_mul ((2:ℝ)^(n-1))).mono'
  · unfold gaussianMoment height
    exact (by fun_prop : Continuous _).aestronglyMeasurable
  · apply Eventually.of_forall
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussianMoment_nonneg n u)]
    have h := add_pow_le (by norm_num : (0:ℝ)≤1) (abs_nonneg u) n
    simpa [gaussianMoment,height,Continuation.polynomialGaussian,mul_assoc] using
      mul_le_mul_of_nonneg_right h (Real.exp_pos (-(u^2))).le

lemma height_sub_le (t v : ℝ) : height t≤height (t+v)*height v := by
  have ht : |t|≤|t+v|+|v| := by
    simpa using (abs_sub_le (t+v) 0 v)
  unfold height
  nlinarith [mul_nonneg (abs_nonneg (t+v)) (abs_nonneg v), abs_nonneg (t+v),abs_nonneg v]

lemma jointHeight_le_shear (t v w : ℝ) :
    jointHeight t v w≤2*height (t+v)*height v*height w := by
  have ht : |t|≤|t+v|+|v| := by simpa using (abs_sub_le (t+v) 0 v)
  have huv : 1≤height (t+v)*height v := one_le_mul_of_one_le_of_one_le (height_one_le _) (height_one_le _)
  have h1 : 1+|t|+|v|≤2*height (t+v)*height v := by
    unfold height
    nlinarith [mul_nonneg (abs_nonneg (t+v)) (abs_nonneg v), abs_nonneg (t+v),abs_nonneg v]
  unfold jointHeight
  change 1+|t|+|v|+|w|≤2*height (t+v)*height v*(1+|w|)
  calc
    _ ≤ 2*height (t+v)*height v+|w| := by linarith [h1]
    _ ≤ 2*height (t+v)*height v+(2*height (t+v)*height v)*|w| := by
      have hh : 1≤2*height (t+v)*height v := by nlinarith
      have hhh := mul_le_mul_of_nonneg_right hh (abs_nonneg w)
      linarith
    _ = _ := by ring

lemma weighted_to_cauchy {f C : ℝ} (J : ℕ) (t : ℝ) (hf : 0≤f)
    (h : height t^(J+2)*f≤C) : height t^J*f≤C*cauchy t := by
  have hh : (1+|t|)^2*(height t^J*f)≤C := by
    simpa [height,pow_add,mul_assoc,mul_comm,mul_left_comm] using h
  exact CubicReflectionKernel.weighted_two_to_cauchy
    (mul_nonneg (pow_nonneg (height_pos t).le _) hf) t hh

lemma weighted_coupled_cauchy (J : ℕ) (t v w A B C D : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (_hD : 0≤D)
    (ha : height v^(J+2)*A≤C) (hb : height w^(J+2)*B≤D) :
    jointHeight t v w^J * Real.exp (-((t+v)^2))*A*B ≤
      (2:ℝ)^J*C*D*(gaussianMoment J (t+v)*cauchy v*cauchy w) := by
  have hpow := pow_le_pow_left₀ (jointHeight_pos t v w).le (jointHeight_le_shear t v w) J
  have ha' := weighted_to_cauchy J v hA ha
  have hb' := weighted_to_cauchy J w hB hb
  calc
    _ ≤ (2*height (t+v)*height v*height w)^J * Real.exp (-((t+v)^2))*A*B := by gcongr
    _ = (2:ℝ)^J * gaussianMoment J (t+v) * (height v^J*A)*(height w^J*B) := by
      simp only [mul_pow,gaussianMoment]
      ring
    _ ≤ (2:ℝ)^J * gaussianMoment J (t+v) * (C*cauchy v)*(D*cauchy w) := by
      have hg := gaussianMoment_nonneg J (t+v)
      have hc := cauchy_nonneg v
      have hd := cauchy_nonneg w
      have hw := (height_pos w).le
      have hv := (height_pos v).le
      gcongr
    _ = _ := by ring

abbrev HeightSpace := (ℝ×ℝ)×ℝ
abbrev heightMeasure : Measure HeightSpace := (volume.prod volume).prod volume

def jointEnvelope (J : ℕ) (p : HeightSpace) : ℝ :=
  gaussianMoment J (p.1.1+p.1.2)*cauchy p.1.2*cauchy p.2

lemma jointEnvelope_nonneg (J : ℕ) (p : HeightSpace) : 0≤jointEnvelope J p := by
  exact mul_nonneg (mul_nonneg (gaussianMoment_nonneg _ _) (cauchy_nonneg _)) (cauchy_nonneg _)

lemma jointEnvelope_integrable (J : ℕ) : Integrable (jointEnvelope J) heightMeasure := by
  have hp : MeasurePreserving (fun p : ℝ×ℝ => (p.1+p.2,p.2))
      (volume.prod volume) (volume.prod volume) := by
    have hp0 : MeasurePreserving (fun p : ℝ×ℝ => (p.2,p.2+p.1))
        (volume.prod volume) (volume.prod volume) := measurePreserving_prod_add_swap volume volume
    have hp1 := (Measure.measurePreserving_swap (μ:=(volume : Measure ℝ)) (ν:=volume)).comp hp0
    simpa only [Function.comp_def,Prod.swap,add_comm] using! hp1
  have ht := hp.prod (MeasurePreserving.id (volume : Measure ℝ))
  have hi := ((gaussianMoment_integrable J).mul_prod cauchy_integrable).mul_prod cauchy_integrable
  exact ht.integrable_comp_of_integrable hi

def onLines (W0 W1 : SchwartzMap ℝ ℂ) (σ ξ υ : ℝ) (p : HeightSpace) : ℂ :=
  profile W0 W1 ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)

lemma onLines_norm (W0 W1 : SchwartzMap ℝ ℂ) (σ ξ υ : ℝ) (p : HeightSpace) :
    ‖onLines W0 W1 σ ξ υ p‖ = Real.exp ((σ+ξ-1)^2)*Real.exp (-((p.1.1+p.1.2)^2))*
      ‖mellin (paperRadialFourier W0) ((ξ:ℂ)+p.1.2*I)‖ *
      ‖mellin W1 ((υ:ℂ)+p.2*I)‖ := by
  unfold onLines profile
  rw [norm_mul,norm_mul,Complex.norm_exp]
  have hr : ((((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1)^2).re =
      (σ+ξ-1)^2+(-((p.1.1+p.1.2)^2)) := by simp [pow_two]; ring
  rw [hr,Real.exp_add]

lemma onLines_continuous (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ)
    (ha1 : 0<a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (σ ξ υ : ℝ) (hξ : 0<ξ) : Continuous (onLines W0 W1 σ ξ υ) := by
  have hR : Continuous (fun t : ℝ => mellin (paperRadialFourier W0) ((ξ:ℂ)+t*I)) :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).continuousOn.comp_continuous
      (by fun_prop) (by intro t; simpa using hξ)
  have hW := (CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1
    (W1.smooth ⊤)).continuous
  unfold onLines profile
  apply Continuous.mul
  · apply Continuous.mul
    · fun_prop
    · exact hR.comp (continuous_snd.comp continuous_fst)
  · exact hW.comp (by fun_prop)

def realGaussianBound (slo shi zlo zhi : ℝ) : ℝ :=
  Real.exp ((|slo|+|shi|+|zlo|+|zhi|+1)^2)
lemma realGaussianBound_pos (slo shi zlo zhi : ℝ) : 0<realGaussianBound slo shi zlo zhi :=
  Real.exp_pos _
lemma realGaussian_le {slo shi zlo zhi σ ξ : ℝ} (hσ : σ∈Icc slo shi) (hξ : ξ∈Icc zlo zhi) :
    Real.exp ((σ+ξ-1)^2)≤realGaussianBound slo shi zlo zhi := by
  have hs : |σ|≤|slo|+|shi| := by
    rw [abs_le]
    constructor <;> linarith [hσ.1,hσ.2,neg_abs_le slo,le_abs_self shi,abs_nonneg slo,abs_nonneg shi]
  have hz : |ξ|≤|zlo|+|zhi| := by
    rw [abs_le]
    constructor <;> linarith [hξ.1,hξ.2,neg_abs_le zlo,le_abs_self zhi,abs_nonneg zlo,abs_nonneg zhi]
  have hh : |σ+ξ-1|≤|slo|+|shi|+|zlo|+|zhi|+1 := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le σ,le_abs_self σ,neg_abs_le ξ,le_abs_self ξ]
  apply Real.exp_le_exp.mpr
  have hp := pow_le_pow_left₀ (abs_nonneg (σ+ξ-1)) hh 2
  simpa [sq_abs] using hp

lemma profile_moment_majorant (W0 W1 : SchwartzMap ℝ ℂ) (J : ℕ)
    {slo shi zlo zhi σ ξ υ C D : ℝ} (hσ : σ∈Icc slo shi) (hξ : ξ∈Icc zlo zhi)
    (hC : 0≤C) (hD : 0≤D)
    (hR : ∀v : ℝ, height v^(J+2)*‖mellin (paperRadialFourier W0) ((ξ:ℂ)+v*I)‖≤C)
    (hW : ∀w : ℝ, height w^(J+2)*‖mellin W1 ((υ:ℂ)+w*I)‖≤D) (p : HeightSpace) :
    jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ ≤
      (realGaussianBound slo shi zlo zhi*2^J*C*D)*jointEnvelope J p := by
  have hb := weighted_coupled_cauchy J p.1.1 p.1.2 p.2
    ‖mellin (paperRadialFourier W0) ((ξ:ℂ)+p.1.2*I)‖ ‖mellin W1 ((υ:ℂ)+p.2*I)‖ C D
    (norm_nonneg _) (norm_nonneg _) hC hD (hR _) (hW _)
  rw [onLines_norm]
  calc
    _ = Real.exp ((σ+ξ-1)^2) * (jointHeight p.1.1 p.1.2 p.2^J*
        Real.exp (-((p.1.1+p.1.2)^2))*
        ‖mellin (paperRadialFourier W0) ((ξ:ℂ)+p.1.2*I)‖*‖mellin W1 ((υ:ℂ)+p.2*I)‖) := by ring
    _ ≤ realGaussianBound slo shi zlo zhi *
        ((2:ℝ)^J*C*D*(gaussianMoment J (p.1.1+p.1.2)*cauchy p.1.2*cauchy p.2)) :=
      mul_le_mul (realGaussian_le hσ hξ) hb
        (by have := (jointHeight_pos p.1.1 p.1.2 p.2).le; positivity)
        (realGaussianBound_pos _ _ _ _).le
    _ = _ := by unfold jointEnvelope; ring

theorem profile_uniform_moments (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      Integrable (fun p : HeightSpace => jointHeight p.1.1 p.1.2 p.2^J*
        ‖onLines W0 W1 σ ξ υ p‖) heightMeasure ∧
      (∫p : HeightSpace, jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)≤K := by
  obtain ⟨C,hC,hR⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0 zlo zhi hzlo (J+2)
  obtain ⟨D,hD,hW⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) wlo whi (J+2)
  let A := realGaussianBound slo shi zlo zhi*2^J*C*D
  have hA : 0<A := by dsimp [A]; exact mul_pos (mul_pos (mul_pos (realGaussianBound_pos _ _ _ _)
    (by positivity)) hC) hD
  refine ⟨A*(1+|∫p, jointEnvelope J p ∂heightMeasure|),by positivity,?_⟩
  intro σ hσ ξ hξ υ hυ
  have hbound := profile_moment_majorant W0 W1 J hσ hξ hC.le hD.le (hR ξ hξ) (hW υ hυ)
  have hc := onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ (hzlo.trans_le hξ.1)
  have hf : Integrable (fun p : HeightSpace => jointHeight p.1.1 p.1.2 p.2^J*
      ‖onLines W0 W1 σ ξ υ p‖) heightMeasure := by
    apply ((jointEnvelope_integrable J).const_mul A).mono'
    · exact ((by unfold jointHeight; fun_prop : Continuous (fun p : HeightSpace =>
        jointHeight p.1.1 p.1.2 p.2^J)).mul hc.norm).aestronglyMeasurable
    · apply Eventually.of_forall
      intro p
      have hn : 0≤jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ :=
        mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)
      rw [Real.norm_eq_abs,abs_of_nonneg hn]
      exact hbound p
  refine ⟨hf,?_⟩
  calc
    _ ≤ ∫p, A*jointEnvelope J p ∂heightMeasure := integral_mono hf
      ((jointEnvelope_integrable J).const_mul A) hbound
    _ = A*(∫p, jointEnvelope J p ∂heightMeasure) := integral_const_mul _ _
    _ ≤ _ := by
      have hh := le_abs_self (∫p, jointEnvelope J p ∂heightMeasure)
      exact mul_le_mul_of_nonneg_left (by linarith) hA.le

def outsideBox (T : ℝ) : Set HeightSpace :=
  {p | T < |p.1.1| ∨ T < |p.1.2| ∨ T < |p.2|}
lemma outsideBox_measurable (T : ℝ) : MeasurableSet (outsideBox T) := by
  unfold outsideBox
  measurability
lemma height_le_joint_on_tail {T : ℝ} {p : HeightSpace} (hp : p∈outsideBox T) :
    1+T≤jointHeight p.1.1 p.1.2 p.2 := by
  rcases hp with h|h|h <;> unfold jointHeight <;>
    linarith [abs_nonneg p.1.1,abs_nonneg p.1.2,abs_nonneg p.2]

lemma weighted_tail_pointwise (f : HeightSpace → ℂ) (J N : ℕ) {T : ℝ} (hT : 0≤T)
    {p : HeightSpace} (hp : p∈outsideBox T) :
    jointHeight p.1.1 p.1.2 p.2^J*‖f p‖ ≤
      (jointHeight p.1.1 p.1.2 p.2^(J+N)*‖f p‖)/(1+T)^N := by
  apply (le_div_iff₀ (by positivity)).mpr
  have hn := pow_le_pow_left₀ (by linarith : 0≤1+T) (height_le_joint_on_tail hp) N
  have hh := mul_le_mul_of_nonneg_left hn
    (mul_nonneg (pow_nonneg (jointHeight_pos p.1.1 p.1.2 p.2).le J) (norm_nonneg (f p)))
  convert hh using 1 ; rw [pow_add] ; ring

theorem profile_uniform_tails (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi, ∀T : ℝ, 0≤T →
      (∫p : HeightSpace in outsideBox T, jointHeight p.1.1 p.1.2 p.2^J*
        ‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)≤K/(1+T)^N := by
  obtain ⟨K,hK,hM⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo (J+N)
  obtain ⟨K0,hK0,hM0⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ T hT
  obtain ⟨hi,hb⟩ := hM σ hσ ξ hξ υ hυ
  have hi0 := (hM0 σ hσ ξ hξ υ hυ).1
  calc
    _ ≤ ∫p : HeightSpace in outsideBox T,
        (jointHeight p.1.1 p.1.2 p.2^(J+N)*‖onLines W0 W1 σ ξ υ p‖)/(1+T)^N ∂heightMeasure := by
      apply setIntegral_mono_on hi0.integrableOn (hi.div_const _).integrableOn (outsideBox_measurable T)
      intro p hp
      exact weighted_tail_pointwise _ J N hT hp
    _ = (∫p : HeightSpace in outsideBox T,
        jointHeight p.1.1 p.1.2 p.2^(J+N)*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)/(1+T)^N :=
      integral_div _ _
    _ ≤ (∫p : HeightSpace,
        jointHeight p.1.1 p.1.2 p.2^(J+N)*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)/(1+T)^N := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply setIntegral_le_integral hi
      exact Eventually.of_forall (fun p => mul_nonneg
        (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _))
    _ ≤ _ := div_le_div_of_nonneg_right hb (by positivity)

theorem profile_arithmetic_integrable (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1) (σ ξ υ : ℝ) (hξ : 0<ξ)
    (G : HeightSpace → ℂ) (hG : AEStronglyMeasurable G heightMeasure) (A : ℝ) (J : ℕ)
    (hbound : ∀p, ‖G p‖≤A*jointHeight p.1.1 p.1.2 p.2^J) :
    Integrable (fun p => G p*onLines W0 W1 σ ξ υ p) heightMeasure := by
  obtain ⟨K,hK,hM⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ σ ξ ξ υ υ hξ J
  have hi := (hM σ ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩).1
  apply (hi.const_mul A).mono'
  · exact hG.mul (onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ hξ).aestronglyMeasurable
  · apply Eventually.of_forall
    intro p
    rw [norm_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound p) (norm_nonneg _)

inductive SliceAxis where
  | s | z | w

def sliceMap (axis : SliceAxis) (T : ℝ) (q : ℝ×ℝ) : HeightSpace :=
  match axis with
  | .s => ((T,q.1),q.2)
  | .z => ((q.1,T),q.2)
  | .w => ((q.1,q.2),T)

lemma sliceMap_continuous (axis : SliceAxis) (T : ℝ) : Continuous (sliceMap axis T) := by
  cases axis <;> unfold sliceMap <;> fun_prop

lemma slice_height_le (axis : SliceAxis) (T : ℝ) (q : ℝ×ℝ) :
    height T≤jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2 := by
  cases axis <;> unfold sliceMap height jointHeight <;>
    linarith [abs_nonneg q.1,abs_nonneg q.2]

lemma cauchy_le_one (t : ℝ) : cauchy t≤1 := by
  simpa [cauchy] using inv_anti₀ (by norm_num : (0:ℝ)<1)
    (show 1≤1+t^2 by nlinarith [sq_nonneg t])

def sliceEnvelope (axis : SliceAxis) (J : ℕ) (T : ℝ) (q : ℝ×ℝ) : ℝ :=
  match axis with
  | .s | .z => gaussianMoment J (T+q.1)*cauchy q.2
  | .w => gaussianMoment J (q.1+q.2)*cauchy q.2

def sliceMass (J : ℕ) : ℝ := (∫u : ℝ, gaussianMoment J u)*(∫v : ℝ, cauchy v)

lemma sliceEnvelope_nonneg (axis : SliceAxis) (J : ℕ) (T : ℝ) (q : ℝ×ℝ) :
    0≤sliceEnvelope axis J T q := by
  cases axis <;> exact mul_nonneg (gaussianMoment_nonneg _ _) (cauchy_nonneg _)

lemma jointEnvelope_slice_le (axis : SliceAxis) (J : ℕ) (T : ℝ) (q : ℝ×ℝ) :
    jointEnvelope J (sliceMap axis T q)≤sliceEnvelope axis J T q := by
  cases axis
  · change gaussianMoment J (T+q.1)*cauchy q.1*cauchy q.2 ≤ gaussianMoment J (T+q.1)*cauchy q.2
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (cauchy_le_one q.1) (gaussianMoment_nonneg J (T+q.1))) (cauchy_nonneg q.2)
    simpa using hh
  · change gaussianMoment J (q.1+T)*cauchy T*cauchy q.2 ≤ gaussianMoment J (T+q.1)*cauchy q.2
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (cauchy_le_one T) (gaussianMoment_nonneg J (q.1+T))) (cauchy_nonneg q.2)
    simpa [add_comm] using hh
  · change gaussianMoment J (q.1+q.2)*cauchy q.2*cauchy T ≤ gaussianMoment J (q.1+q.2)*cauchy q.2
    simpa using mul_le_mul_of_nonneg_left (cauchy_le_one T)
      (mul_nonneg (gaussianMoment_nonneg _ _) (cauchy_nonneg _))

lemma pairEnvelope_integrable (J : ℕ) :
    Integrable (fun q : ℝ×ℝ => gaussianMoment J (q.1+q.2)*cauchy q.2) (volume.prod volume) := by
  have hp0 : MeasurePreserving (fun p : ℝ×ℝ => (p.2,p.2+p.1))
      (volume.prod volume) (volume.prod volume) := measurePreserving_prod_add_swap volume volume
  have hp1 := (Measure.measurePreserving_swap (μ:=(volume : Measure ℝ)) (ν:=volume)).comp hp0
  have hi := hp1.integrable_comp_of_integrable ((gaussianMoment_integrable J).mul_prod cauchy_integrable)
  simpa only [Function.comp_def,Prod.swap,add_comm] using! hi

lemma sliceEnvelope_integrable (axis : SliceAxis) (J : ℕ) (T : ℝ) :
    Integrable (sliceEnvelope axis J T) (volume.prod volume) := by
  cases axis
  · exact ((gaussianMoment_integrable J).comp_add_left T).mul_prod cauchy_integrable
  · exact ((gaussianMoment_integrable J).comp_add_left T).mul_prod cauchy_integrable
  · exact pairEnvelope_integrable J

lemma sliceEnvelope_integral (axis : SliceAxis) (J : ℕ) (T : ℝ) :
    (∫q : ℝ×ℝ, sliceEnvelope axis J T q ∂volume.prod volume)=sliceMass J := by
  cases axis
  · change (∫q : ℝ×ℝ, gaussianMoment J (T+q.1)*cauchy q.2 ∂volume.prod volume)=_
    rw [integral_prod_mul (fun u : ℝ => gaussianMoment J (T+u)) cauchy,integral_add_left_eq_self]
    rfl
  · change (∫q : ℝ×ℝ, gaussianMoment J (T+q.1)*cauchy q.2 ∂volume.prod volume)=_
    rw [integral_prod_mul (fun u : ℝ => gaussianMoment J (T+u)) cauchy,integral_add_left_eq_self]
    rfl
  · change (∫q : ℝ×ℝ, gaussianMoment J (q.1+q.2)*cauchy q.2 ∂volume.prod volume)=_
    rw [integral_prod_symm _ (pairEnvelope_integrable J)]
    simp_rw [integral_mul_const,integral_add_right_eq_self]
    exact integral_const_mul _ _

lemma weighted_slice_pointwise (f : HeightSpace → ℂ) (axis : SliceAxis) (J N : ℕ) (T : ℝ) (q : ℝ×ℝ) :
    jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J*
      ‖f (sliceMap axis T q)‖ ≤
    (jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^(J+N)*
      ‖f (sliceMap axis T q)‖)/height T^N := by
  apply (le_div_iff₀ (pow_pos (height_pos T) N)).mpr
  have hn := pow_le_pow_left₀ (height_pos T).le (slice_height_le axis T q) N
  have hh := mul_le_mul_of_nonneg_left hn
    (mul_nonneg (pow_nonneg (jointHeight_pos (sliceMap axis T q).1.1
      (sliceMap axis T q).1.2 (sliceMap axis T q).2).le J) (norm_nonneg (f (sliceMap axis T q))))
  convert hh using 1 ; rw [pow_add] ; ring

theorem profile_uniform_slices (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      ∀axis : SliceAxis, ∀T : ℝ,
      Integrable (fun q : ℝ×ℝ =>
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J*
        ‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J*
        ‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖ ∂volume.prod volume)≤K/height T^N := by
  obtain ⟨C,hC,hR⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0
    zlo zhi hzlo (J+N+2)
  obtain ⟨D,hD,hW⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) wlo whi (J+N+2)
  let A := realGaussianBound slo shi zlo zhi*2^(J+N)*C*D
  have hA : 0<A := by dsimp [A]; exact mul_pos (mul_pos (mul_pos (realGaussianBound_pos _ _ _ _)
    (by positivity)) hC) hD
  refine ⟨A*(1+|sliceMass (J+N)|),by positivity,?_⟩
  intro σ hσ ξ hξ υ hυ axis T
  have hb := profile_moment_majorant W0 W1 (J+N) hσ hξ hC.le hD.le (hR ξ hξ) (hW υ hυ)
  let f (q : ℝ×ℝ) := jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
    (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖
  have hbound (q : ℝ×ℝ) : f q≤(A/height T^N)*sliceEnvelope axis (J+N) T q := by
    calc
      _ ≤ (jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^(J+N)*
          ‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖)/height T^N :=
        weighted_slice_pointwise _ axis J N T q
      _ ≤ (A*jointEnvelope (J+N) (sliceMap axis T q))/height T^N :=
        div_le_div_of_nonneg_right (hb _) (pow_nonneg (height_pos T).le N)
      _ ≤ (A*sliceEnvelope axis (J+N) T q)/height T^N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (jointEnvelope_slice_le _ _ _ _) hA.le)
          (pow_nonneg (height_pos T).le N)
      _ = _ := by ring
  have hfnonneg (q : ℝ×ℝ) : 0≤f q := mul_nonneg
    (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)
  have hf : Integrable f (volume.prod volume) := by
    apply ((sliceEnvelope_integrable axis (J+N) T).const_mul (A/height T^N)).mono'
    · have hc := (onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ
        (hzlo.trans_le hξ.1)).comp (sliceMap_continuous axis T)
      exact ((by cases axis <;> unfold sliceMap jointHeight <;> fun_prop : Continuous (fun q : ℝ×ℝ =>
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J)).mul hc.norm).aestronglyMeasurable
    · exact Eventually.of_forall (fun q => by rw [Real.norm_eq_abs,abs_of_nonneg (hfnonneg q)]; exact hbound q)
  refine ⟨hf,?_⟩
  calc
    _ ≤ ∫q : ℝ×ℝ, (A/height T^N)*sliceEnvelope axis (J+N) T q ∂volume.prod volume :=
      integral_mono hf ((sliceEnvelope_integrable axis (J+N) T).const_mul _) hbound
    _ = (A/height T^N)*sliceMass (J+N) := by rw [integral_const_mul,sliceEnvelope_integral]
    _ ≤ (A/height T^N)*(1+|sliceMass (J+N)|) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hA.le (pow_nonneg (height_pos T).le N))
      linarith [le_abs_self (sliceMass (J+N))]
    _ = _ := by ring

theorem profile_arithmetic_tails (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      ∀A : ℝ, 0≤A → ∀G : HeightSpace → ℂ,
      AEStronglyMeasurable G heightMeasure →
      (∀p, ‖G p‖≤A*jointHeight p.1.1 p.1.2 p.2^J) →
      Integrable (fun p => G p*onLines W0 W1 σ ξ υ p) heightMeasure ∧
      ∀T : ℝ, 0≤T →
      (∫p : HeightSpace in outsideBox T, ‖G p*onLines W0 W1 σ ξ υ p‖ ∂heightMeasure)
        ≤ A*K/(1+T)^N := by
  obtain ⟨K,hK,hT⟩ := profile_uniform_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J N
  obtain ⟨K0,hK0,hM⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ A hA G hG hbound
  have hi := profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ ξ υ (hzlo.trans_le hξ.1) G hG A J hbound
  refine ⟨hi,?_⟩
  intro T hT0
  calc
    _ ≤ ∫p : HeightSpace in outsideBox T,
        A*(jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖) ∂heightMeasure := by
      apply setIntegral_mono_on hi.norm.integrableOn
        (((hM σ hσ ξ hξ υ hυ).1).const_mul A).integrableOn (outsideBox_measurable T)
      intro p hp
      rw [norm_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound p) (norm_nonneg _)
    _ = A*(∫p : HeightSpace in outsideBox T,
        jointHeight p.1.1 p.1.2 p.2^J*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure) :=
      integral_const_mul _ _
    _ ≤ A*(K/(1+T)^N) := mul_le_mul_of_nonneg_left (hT σ hσ ξ hξ υ hυ T hT0) hA
    _ = _ := by ring

theorem profile_arithmetic_slices (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃ K : ℝ, 0<K ∧ ∀σ∈Icc slo shi, ∀ξ∈Icc zlo zhi, ∀υ∈Icc wlo whi,
      ∀axis : SliceAxis, ∀T A : ℝ, 0≤A → ∀G : ℝ×ℝ → ℂ,
      AEStronglyMeasurable G (volume.prod volume) →
      (∀q, ‖G q‖≤A*jointHeight (sliceMap axis T q).1.1
        (sliceMap axis T q).1.2 (sliceMap axis T q).2^J) →
      Integrable (fun q => G q*onLines W0 W1 σ ξ υ (sliceMap axis T q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ, ‖G q*onLines W0 W1 σ ξ υ (sliceMap axis T q)‖ ∂volume.prod volume)
        ≤ A*K/height T^N := by
  obtain ⟨K,hK,hM⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J N
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ axis T A hA G hG hbound
  obtain ⟨hm,hmb⟩ := hM σ hσ ξ hξ υ hυ axis T
  have hdom (q : ℝ×ℝ) : ‖G q*onLines W0 W1 σ ξ υ (sliceMap axis T q)‖≤
      A*(jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
        (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖) := by
    rw [norm_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hbound q) (norm_nonneg _)
  have hi : Integrable (fun q => G q*onLines W0 W1 σ ξ υ (sliceMap axis T q))
      (volume.prod volume) := by
    apply (hm.const_mul A).mono'
    · exact hG.mul (((onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ
        (hzlo.trans_le hξ.1)).comp (sliceMap_continuous axis T)).aestronglyMeasurable)
    · exact Eventually.of_forall hdom
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫q : ℝ×ℝ,
        A*(jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
          (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖) ∂volume.prod volume :=
      integral_mono hi.norm (hm.const_mul A) hdom
    _ = A*(∫q : ℝ×ℝ,
        jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2
          (sliceMap axis T q).2^J*‖onLines W0 W1 σ ξ υ (sliceMap axis T q)‖ ∂volume.prod volume) :=
      integral_const_mul _ _
    _ ≤ A*(K/height T^N) := mul_le_mul_of_nonneg_left hmb hA
    _ = _ := by ring

theorem profile_arithmetic_fubini (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1) (σ ξ υ : ℝ) (hξ : 0<ξ)
    (G : HeightSpace → ℂ) (hG : AEStronglyMeasurable G heightMeasure) (A : ℝ) (J : ℕ)
    (hbound : ∀p, ‖G p‖≤A*jointHeight p.1.1 p.1.2 p.2^J) :
    ((∫p : HeightSpace, G p*onLines W0 W1 σ ξ υ p ∂heightMeasure) =
      ∫τ : ℝ, ∫ν : ℝ, ∫ω : ℝ, G ((τ,ν),ω)*onLines W0 W1 σ ξ υ ((τ,ν),ω)) ∧
    ((∫p : HeightSpace, G p*onLines W0 W1 σ ξ υ p ∂heightMeasure) =
      ∫ω : ℝ, ∫ν : ℝ, ∫τ : ℝ, G ((τ,ν),ω)*onLines W0 W1 σ ξ υ ((τ,ν),ω)) := by
  have hi := profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ ξ υ hξ G hG A J hbound
  constructor
  · rw [integral_prod _ hi]
    exact integral_prod _ hi.integral_prod_left
  · rw [integral_prod_symm _ hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with ω hω
    exact integral_prod_symm _ hω

end SevenEighths.ProbeMellinBoundary

end

end OAI
