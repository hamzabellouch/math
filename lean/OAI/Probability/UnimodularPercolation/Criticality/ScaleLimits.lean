import Mathlib

namespace OAI

/-! Analytic scale limits and quantitative parameter estimates. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open Filter
open scoped Topology

 

theorem log_sublinear_of_subexp (f : ℕ → ℝ) (hf : ∀ n, 1 ≤ f n)
    (hb : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 < K ∧ ∀ n, f n ≤ K*Real.exp (η*(n:ℝ))) :
    Tendsto (fun n => Real.log (f n)/(n:ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K,hK,hbK⟩ := hb (ε/2) (half_pos hε)
  have hlim := tendsto_const_div_atTop_nhds_zero_nat (Real.log K)
  filter_upwards [hlim.eventually (gt_mem_nhds (half_pos hε)), eventually_ge_atTop (1:ℕ)] with n hn hn1
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hlog := Real.log_le_log (zero_lt_one.trans_le (hf n)) (hbK n)
  rw [Real.log_mul hK.ne' (Real.exp_pos _).ne',Real.log_exp] at hlog
  have hdiv := (div_le_div_of_nonneg_right hlog hnpos.le)
  rw [add_div,mul_div_cancel_right₀ _ hnpos.ne'] at hdiv
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (Real.log_nonneg (hf n)) hnpos.le)]
  linarith only [hdiv,hn]

 
theorem tendsto_atTop_of_div_nat_pos (f : ℕ → ℝ) (L : ℝ) (hL : 0 < L)
    (hf : Tendsto (fun n => f n/(n:ℝ)) atTop (𝓝 L)) : Tendsto f atTop atTop := by
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_pos hL hf
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  exact mul_div_cancel₀ (f n) (by exact_mod_cast (show n ≠ 0 by omega))

 
theorem tendsto_exp_of_div_nat_neg (f : ℕ → ℝ) (L : ℝ) (hL : L < 0)
    (hf : Tendsto (fun n => f n/(n:ℝ)) atTop (𝓝 L)) :
    Tendsto (fun n => Real.exp (f n)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n => -f n/(n:ℝ)) atTop (𝓝 (-L)) := by
    simpa only [neg_div] using hf.neg
  have ht := tendsto_atTop_of_div_nat_pos (fun n => -f n) (-L) (neg_pos.mpr hL) hn
  simpa only [Function.comp_def,neg_neg] using Real.tendsto_exp_neg_atTop_nhds_zero.comp ht

 

theorem corridor_scale_limits (r C₁ : ℝ) (J : ℕ) (hr : 0 < r) (hC₁ : 0 < C₁) (hJ : 0 < J)
    (R : ℕ → ℝ) (hR : ∀ n, 1 ≤ R n)
    (hlogR : Tendsto (fun n => Real.log (R n)/(n:ℝ)) atTop (𝓝 0)) :
    let k := fun n : ℕ => ⌈r*(n:ℝ)⌉₊
    let j := fun n : ℕ => J+⌈C₁*Real.log (((k n:ℝ)+1)*R n)⌉₊
    Tendsto k atTop atTop ∧
    Tendsto (fun n => (k n:ℝ)/(n:ℝ)) atTop (𝓝 r) ∧
    Tendsto (fun n => (j n:ℝ)/(n:ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n => Real.log (j n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
  dsimp only
  let k := fun n : ℕ => ⌈r*(n:ℝ)⌉₊
  let j := fun n : ℕ => J+⌈C₁*Real.log (((k n:ℝ)+1)*R n)⌉₊
  have hkt : Tendsto k atTop atTop :=
    tendsto_nat_ceil_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hr)
  have hk : Tendsto (fun n => (k n:ℝ)/(n:ℝ)) atTop (𝓝 r) :=
    (tendsto_nat_ceil_mul_div_atTop hr.le).comp tendsto_natCast_atTop_atTop
  have hkplus : Tendsto (fun n => ((k n:ℝ)+1)/(n:ℝ)) atTop (𝓝 r) := by
    simpa only [add_div,add_zero] using hk.add (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
  have hkTop : Tendsto (fun n => (k n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_of_nonneg_right (show (0:ℝ) ≤ 1 by norm_num))
      (tendsto_natCast_atTop_atTop.comp hkt)
  have hlogk : Tendsto (fun n => Real.log ((k n:ℝ)+1)/(n:ℝ)) atTop (𝓝 0) := by
    have hl : Tendsto (fun n => Real.log ((k n:ℝ)+1)/((k n:ℝ)+1)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,pow_one,one_mul,add_zero] using
        (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp hkTop
    have hh := hl.mul hkplus
    rw [zero_mul] at hh
    apply hh.congr
    intro n
    have hn : (k n:ℝ)+1 ≠ 0 := by positivity
    field_simp
  have hupper : Tendsto (fun n : ℕ => ((J:ℝ)+1)/(n:ℝ) + C₁*(Real.log ((k n:ℝ)+1)/(n:ℝ) + Real.log (R n)/(n:ℝ))) atTop (𝓝 0) := by
    simpa only [add_zero,mul_zero] using
      (tendsto_const_div_atTop_nhds_zero_nat ((J:ℝ)+1)).add ((hlogk.add hlogR).const_mul C₁)
  have hjlim : Tendsto (fun n => (j n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · exact Eventually.of_forall (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hprod : 1 ≤ ((k n:ℝ)+1)*R n := by nlinarith only [hR n,(Nat.cast_nonneg (k n) : (0:ℝ) ≤ _)]
    have harg : 0 ≤ C₁*Real.log (((k n:ℝ)+1)*R n) := mul_nonneg hC₁.le (Real.log_nonneg hprod)
    have hceil := (Nat.ceil_lt_add_one harg).le
    have he : Real.log (((k n:ℝ)+1)*R n) = Real.log ((k n:ℝ)+1)+Real.log (R n) :=
      Real.log_mul (by positivity) (zero_lt_one.trans_le (hR n)).ne'
    dsimp only [j]
    push_cast
    rw [←add_div,←mul_div_assoc,←add_div,←he]
    exact (div_le_div_of_nonneg_right (by linarith only [hceil]) hnpos.le)
  refine ⟨hkt,hk,hjlim,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hjlim
  · exact Eventually.of_forall (fun n => div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr (show 1 ≤ j n by dsimp [j]; omega))) (Nat.cast_nonneg n))
  · exact Eventually.of_forall (fun n => div_le_div_of_nonneg_right (Real.log_le_self (Nat.cast_nonneg (j n))) (Nat.cast_nonneg n))

 

theorem exists_corridor_scales_of_slopes
    (ρ p₀ C C₁ ε M cm r z : ℝ) (J k₀ : ℕ)
    (hρ : 0 < ρ) (hp₀ : 0 < p₀) (hC₁ : 0 < C₁) (hε : 0 < ε) (hcm : 0 < cm)
    (hJ : 0 < J) (hr : 0 < r) (hz : 0 < z)
    (hzρ : z+r*Real.log ρ < 0) (hzC : z+C*r < 1)
    (m R Q : ℕ → ℝ) (hR : ∀ n, 1 ≤ R n) (hQ : ∀ n, 1 ≤ Q n)
    (hm : ∀ n : ℕ, cm*Real.exp (n:ℝ) ≤ m n)
    (hlogR : Tendsto (fun n => Real.log (R n)/(n:ℝ)) atTop (𝓝 0))
    (hlogQ : Tendsto (fun n => Real.log (Q n)/(n:ℝ)) atTop (𝓝 0)) :
    ∃ (n k : ℕ) (B : ℝ), k₀ ≤ k ∧ 0 < B ∧
      let j := J+⌈C₁*Real.log (((k:ℝ)+1)*R n)⌉₊
      B*ρ^k ≤ 1/4 ∧ B*(j:ℝ)*Real.exp (C*(k:ℝ)) ≤ m n ∧
      (R n)^2*Q n*ρ^k ≤ ε*p₀^(2*j) ∧ M < B*p₀^(2*j) := by
  let k := fun n : ℕ => ⌈r*(n:ℝ)⌉₊
  let j := fun n : ℕ => J+⌈C₁*Real.log (((k n:ℝ)+1)*R n)⌉₊
  let B := fun n : ℕ => Real.exp (z*(n:ℝ))
  obtain ⟨hkt,hk,hj,hlogj⟩ := corridor_scale_limits r C₁ J hr hC₁ hJ R hR hlogR
  change Tendsto k atTop atTop at hkt
  change Tendsto (fun n => (k n:ℝ)/(n:ℝ)) atTop (𝓝 r) at hk
  change Tendsto (fun n => (j n:ℝ)/(n:ℝ)) atTop (𝓝 0) at hj
  change Tendsto (fun n => Real.log (j n:ℝ)/(n:ℝ)) atTop (𝓝 0) at hlogj
  have hn : Tendsto (fun n : ℕ => (n:ℝ)/(n:ℝ)) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_natCast_div_add_atTop (0:ℝ)
  have hβ (n) : Real.exp ((j n:ℝ)*(2*Real.log p₀)) = p₀^(2*j n) := by
    rw [show (j n:ℝ)*(2*Real.log p₀) = ((2*j n:ℕ):ℝ)*Real.log p₀ by push_cast; ring,
      Real.exp_nat_mul,Real.exp_log hp₀]
  have hjpos (n) : (0:ℝ) < j n := Nat.cast_pos.mpr (by dsimp [j]; omega)
  have hlim₁ : Tendsto (fun n : ℕ => (z*(n:ℝ)+(k n:ℝ)*Real.log ρ)/(n:ℝ)) atTop (𝓝 (z+r*Real.log ρ)) := by
    simpa only [mul_one,div_mul_eq_mul_div,←mul_div_assoc,←add_div] using
      (hn.const_mul z).add (hk.mul_const (Real.log ρ))
  have hdec₁ := tendsto_exp_of_div_nat_neg _ _ hzρ hlim₁
  have hlim₂ : Tendsto (fun n : ℕ =>
      (2*Real.log (R n)+Real.log (Q n)+(k n:ℝ)*Real.log ρ-(j n:ℝ)*(2*Real.log p₀))/(n:ℝ))
      atTop (𝓝 (r*Real.log ρ)) := by
    simpa only [mul_zero,zero_add,zero_mul,sub_zero,div_mul_eq_mul_div,←mul_div_assoc,←add_div,←sub_div] using
      (((hlogR.const_mul 2).add hlogQ).add (hk.mul_const (Real.log ρ))).sub (hj.mul_const (2*Real.log p₀))
  have hsl₂ : r*Real.log ρ < 0 := by linarith only [hz,hzρ]
  have hdec₂ := tendsto_exp_of_div_nat_neg _ _ hsl₂ hlim₂
  have hlim₃ : Tendsto (fun n : ℕ =>
      (z*(n:ℝ)+Real.log (j n:ℝ)+C*(k n:ℝ)-(n:ℝ))/(n:ℝ)) atTop (𝓝 (z+C*r-1)) := by
    simpa only [mul_one,add_zero,←mul_div_assoc,←add_div,←sub_div] using
      (((hn.const_mul z).add hlogj).add (hk.const_mul C)).sub hn
  have hdec₃ := tendsto_exp_of_div_nat_neg _ _ (sub_neg.mpr hzC) hlim₃
  have hlim₄ : Tendsto (fun n : ℕ =>
      (z*(n:ℝ)+(j n:ℝ)*(2*Real.log p₀))/(n:ℝ)) atTop (𝓝 z) := by
    simpa only [mul_one,zero_mul,add_zero,div_mul_eq_mul_div,←mul_div_assoc,←add_div] using
      (hn.const_mul z).add (hj.mul_const (2*Real.log p₀))
  have hgrow := Real.tendsto_exp_atTop.comp (tendsto_atTop_of_div_nat_pos _ _ hz hlim₄)
  have hfinal : ∀ᶠ n : ℕ in atTop,
      k₀ ≤ k n ∧ B n*ρ^(k n) ≤ 1/4 ∧
      B n*(j n:ℝ)*Real.exp (C*(k n:ℝ)) ≤ m n ∧
      (R n)^2*Q n*ρ^(k n) ≤ ε*p₀^(2*j n) ∧ M < B n*p₀^(2*j n) := by
    filter_upwards [hkt.eventually_ge_atTop k₀,
      hdec₁.eventually_lt_const (show (0:ℝ) < 1/4 by norm_num),
      hdec₂.eventually_lt_const hε,hdec₃.eventually_lt_const hcm,
      hgrow.eventually_gt_atTop M] with n hk₀ h₁ h₂ h₃ h₄
    have heρ : Real.exp ((k n:ℝ)*Real.log ρ) = ρ^(k n) := by rw [Real.exp_nat_mul,Real.exp_log hρ]
    have heR : Real.exp (2*Real.log (R n)) = (R n)^2 := by
      simpa only [Nat.cast_ofNat,Real.exp_log (zero_lt_one.trans_le (hR n))] using Real.exp_nat_mul (Real.log (R n)) 2
    simp only [Real.exp_add,heρ] at h₁
    simp only [Real.exp_sub,Real.exp_add,heR,Real.exp_log (zero_lt_one.trans_le (hQ n)),heρ,hβ n] at h₂
    simp only [Real.exp_sub,Real.exp_add,Real.exp_log (hjpos n)] at h₃
    change M < Real.exp (z*(n:ℝ)+(j n:ℝ)*(2*Real.log p₀)) at h₄
    rw [Real.exp_add,hβ n] at h₄
    refine ⟨hk₀,h₁.le,?_,(div_le_iff₀ (pow_pos hp₀ _)).mp h₂.le,h₄⟩
    exact ((div_le_iff₀ (Real.exp_pos _)).mp h₃.le).trans (hm n)
  obtain ⟨n,hn⟩ := hfinal.exists
  exact ⟨n,k n,B n,hn.1,Real.exp_pos _,hn.2⟩

 

theorem exists_corridor_scales
    (ρ p₀ C C₁ ε M cm : ℝ) (J k₀ : ℕ)
    (hρ : 0 < ρ) (hρ₁ : ρ < 1) (hp₀ : 0 < p₀) (hC : 0 < C)
    (hC₁ : 0 < C₁) (hε : 0 < ε) (hcm : 0 < cm) (hJ : 0 < J)
    (m R Q : ℕ → ℝ) (hR : ∀ n, 1 ≤ R n) (hQ : ∀ n, 1 ≤ Q n)
    (hm : ∀ n : ℕ, cm*Real.exp (n:ℝ) ≤ m n)
    (hlogR : Tendsto (fun n => Real.log (R n)/(n:ℝ)) atTop (𝓝 0))
    (hlogQ : Tendsto (fun n => Real.log (Q n)/(n:ℝ)) atTop (𝓝 0)) :
    ∃ (n k : ℕ) (B : ℝ), k₀ ≤ k ∧ 0 < B ∧
      let j := J+⌈C₁*Real.log (((k:ℝ)+1)*R n)⌉₊
      B*ρ^k ≤ 1/4 ∧ B*(j:ℝ)*Real.exp (C*(k:ℝ)) ≤ m n ∧
      (R n)^2*Q n*ρ^k ≤ ε*p₀^(2*j) ∧ M < B*p₀^(2*j) := by
  let r := 1/(4*(C+1))
  let z := min (1/4) (-(r*Real.log ρ)/2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hlog : Real.log ρ < 0 := by simpa only [Real.log_one] using Real.log_lt_log hρ hρ₁
  have hz : 0 < z := lt_min (by norm_num) (half_pos (neg_pos.mpr (mul_neg_of_pos_of_neg hr hlog)))
  have hzr : z+r*Real.log ρ < 0 := by
    have hh : z ≤ -(r*Real.log ρ)/2 := min_le_right _ _
    linarith only [hh,mul_neg_of_pos_of_neg hr hlog]
  have hzc : z+C*r < 1 := by
    have hz' : z ≤ 1/4 := min_le_left _ _
    have hr' : r*(4*(C+1)) = 1 := div_mul_cancel₀ 1 (by positivity)
    nlinarith only [hz',hr',hr]
  exact exists_corridor_scales_of_slopes ρ p₀ C C₁ ε M cm r z J k₀
    hρ hp₀ hC₁ hε hcm hJ hr hz hzr hzc m R Q hR hQ hm hlogR hlogQ

end Percolation

end OAI
