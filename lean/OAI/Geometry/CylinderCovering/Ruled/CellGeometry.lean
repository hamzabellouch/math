import OAI.Geometry.CylinderCovering.Ruled.CellsDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ProductCells

lemma closedCell_isClosed (A B : ℝ) : IsClosed (closedCell A B) := by
  exact (isClosed_le (continuous_fst.abs) continuous_const).inter
    ((isClosed_le (continuous_snd.abs) continuous_const).inter
      (isClosed_le ((continuous_fst.mul continuous_snd).abs) continuous_const))

lemma openCell_isOpen (A B : ℝ) : IsOpen (openCell A B) := by
  exact (isOpen_lt (continuous_fst.abs) continuous_const).inter
    ((isOpen_lt (continuous_snd.abs) continuous_const).inter
      (isOpen_lt ((continuous_fst.mul continuous_snd).abs) continuous_const))

lemma closedCell_subset_box (A B : ℝ) :
    closedCell A B ⊆ Icc (-A, -A) (A, A) := by
  rintro ⟨x,y⟩ ⟨hx,hy,hxy⟩
  exact ⟨⟨(abs_le.mp hx).1, (abs_le.mp hy).1⟩,
    ⟨(abs_le.mp hx).2, (abs_le.mp hy).2⟩⟩

lemma closedCell_isCompact (A B : ℝ) : IsCompact (closedCell A B) :=
  isCompact_Icc.of_isClosed_subset (closedCell_isClosed A B) (closedCell_subset_box A B)

lemma openCell_subset_closedCell (A B : ℝ) : openCell A B ⊆ closedCell A B := by
  rintro p ⟨hx,hy,hxy⟩
  exact ⟨hx.le,hy.le,hxy.le⟩

lemma openCell_isBounded (A B : ℝ) : Bornology.IsBounded (openCell A B) :=
  (closedCell_isCompact A B).isBounded.subset (openCell_subset_closedCell A B)

lemma dilation_closedCell (m A B : ℝ) (hm : 0 < m) :
    dilation m '' closedCell A B = closedCell (m*A) (m^2*B) := by
  ext p
  constructor
  · rintro ⟨q,⟨hx,hy,hxy⟩,rfl⟩
    dsimp [closedCell, dilation] at *
    rw [abs_mul, abs_of_pos hm, abs_mul, abs_of_pos hm]
    refine ⟨mul_le_mul_of_nonneg_left hx hm.le,
      mul_le_mul_of_nonneg_left hy hm.le, ?_⟩
    calc |m*q.1*(m*q.2)| = m^2*|q.1*q.2| := by
          rw [show m*q.1*(m*q.2)=m^2*(q.1*q.2) by ring,
            abs_mul, abs_of_nonneg (sq_nonneg m)]
         _ ≤ m^2*B := mul_le_mul_of_nonneg_left hxy (sq_nonneg m)
  · intro hp
    refine ⟨(p.1/m,p.2/m), ?_, ?_⟩
    · rcases hp with ⟨hx,hy,hxy⟩
      dsimp [closedCell]
      rw [abs_div,abs_div,abs_of_pos hm]
      refine ⟨(div_le_iff₀ hm).mpr (by simpa [mul_comm] using hx),
        (div_le_iff₀ hm).mpr (by simpa [mul_comm] using hy), ?_⟩
      rw [div_mul_div_comm,abs_div,abs_of_pos (mul_pos hm hm)]
      apply (div_le_iff₀ (mul_pos hm hm)).mpr
      simpa [pow_two,mul_comm] using hxy
    · ext <;> dsimp [dilation] <;> field_simp

lemma dilation_openCell (m A B : ℝ) (hm : 0 < m) :
    dilation m '' openCell A B = openCell (m*A) (m^2*B) := by
  ext p
  constructor
  · rintro ⟨q,⟨hx,hy,hxy⟩,rfl⟩
    dsimp [openCell, dilation] at *
    rw [abs_mul, abs_of_pos hm, abs_mul, abs_of_pos hm]
    refine ⟨mul_lt_mul_of_pos_left hx hm,
      mul_lt_mul_of_pos_left hy hm, ?_⟩
    calc |m*q.1*(m*q.2)| = m^2*|q.1*q.2| := by
          rw [show m*q.1*(m*q.2)=m^2*(q.1*q.2) by ring,
            abs_mul, abs_of_nonneg (sq_nonneg m)]
         _ < m^2*B := mul_lt_mul_of_pos_left hxy (sq_pos_of_pos hm)
  · intro hp
    refine ⟨(p.1/m,p.2/m), ?_, ?_⟩
    · rcases hp with ⟨hx,hy,hxy⟩
      dsimp [openCell]
      rw [abs_div,abs_div,abs_of_pos hm]
      refine ⟨(div_lt_iff₀ hm).mpr (by simpa [mul_comm] using hx),
        (div_lt_iff₀ hm).mpr (by simpa [mul_comm] using hy), ?_⟩
      rw [div_mul_div_comm,abs_div,abs_of_pos (mul_pos hm hm)]
      apply (div_lt_iff₀ (mul_pos hm hm)).mpr
      simpa [pow_two,mul_comm] using hxy
    · ext <;> dsimp [dilation] <;> field_simp

lemma logarithmicCell_eq_dilation (m : ℝ) (hm : 0 < m) :
    logarithmicCell m = dilation m '' parameterCell (1/m^2) := by
  rw [parameterCell, dilation_closedCell m 1 (1/m^2) hm]
  simp [logarithmicCell, ne_of_gt hm]

lemma logarithmicIntercept_eq_dilation (m gamma : ℝ) (hm : 0 < m) :
    logarithmicIntercept m gamma = dilation m '' interceptCell (1/m^2) gamma := by
  rw [interceptCell, dilation_openCell m 3 ((1+gamma)*(1/m^2)) hm]
  have h : m^2*((1+gamma)*(1/m^2)) = 1+gamma := by field_simp
  rw [h]
  simp only [logarithmicIntercept,mul_comm]

lemma opposite_expansion_bounds {z s₁ s₂ tau : ℝ}
    (hz : |z| ≤ 1) (hs₁ : |s₁| ≤ 1) (hs₂ : |s₂| ≤ 1)
    (hs : |s₁*s₂| ≤ tau) :
    |(1+z)*s₁| ≤ 2 ∧ |(1-z)*s₂| ≤ 2 ∧
      |((1+z)*s₁)*((1-z)*s₂)| ≤ tau := by
  have hz' := abs_le.mp hz
  have hplus : |1+z| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hminus : |1-z| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hcoef : 0 ≤ 1-z^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-z) (by linarith : 0 ≤ 1+z)]
  refine ⟨?_,?_,?_⟩
  · rw [abs_mul]
    nlinarith [mul_le_mul hplus hs₁ (abs_nonneg s₁) (by norm_num : (0:ℝ) ≤ 2)]
  · rw [abs_mul]
    nlinarith [mul_le_mul hminus hs₂ (abs_nonneg s₂) (by norm_num : (0:ℝ) ≤ 2)]
  · rw [show ((1+z)*s₁)*((1-z)*s₂)=(1-z^2)*(s₁*s₂) by ring,
      abs_mul, abs_of_nonneg hcoef]
    nlinarith [mul_nonneg (sq_nonneg z) (abs_nonneg (s₁*s₂))]

lemma perturbed_product_bounds {u₁ u₂ e₁ e₂ eps tau gamma : ℝ}
    (hu₁ : |u₁| ≤ 2) (hu₂ : |u₂| ≤ 2) (hu : |u₁*u₂| ≤ tau)
    (he₁ : |e₁| ≤ eps) (he₂ : |e₂| ≤ eps)
    (heps : eps < 1/2) (hgap : eps < gamma*tau/5) :
    |u₁+e₁| < 3 ∧ |u₂+e₂| < 3 ∧
      |(u₁+e₁)*(u₂+e₂)| < (1+gamma)*tau := by
  have heps0 : 0 ≤ eps := (abs_nonneg e₁).trans he₁
  have h₁ : |u₁*e₂| ≤ 2*eps := by
    rw [abs_mul]
    exact mul_le_mul hu₁ he₂ (abs_nonneg e₂) (by norm_num)
  have h₂ : |e₁*u₂| ≤ 2*eps := by
    rw [abs_mul]
    nlinarith [mul_le_mul he₁ hu₂ (abs_nonneg u₂) heps0]
  have h₃ : |e₁*e₂| ≤ eps^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul he₁ he₂ (abs_nonneg e₂) heps0
  refine ⟨lt_of_le_of_lt (abs_add_le u₁ e₁) (by linarith),
    lt_of_le_of_lt (abs_add_le u₂ e₂) (by linarith), ?_⟩
  have hsum : |(u₁+e₁)*(u₂+e₂)| ≤ tau+4*eps+eps^2 := by
    calc |(u₁+e₁)*(u₂+e₂)|
        = |((u₁*u₂+u₁*e₂)+e₁*u₂)+e₁*e₂| := by congr 1; ring
      _ ≤ |u₁*u₂+u₁*e₂|+|e₁*u₂|+|e₁*e₂| := by
          have h := abs_add_le (u₁*u₂+u₁*e₂) (e₁*u₂)
          have h' := abs_add_le ((u₁*u₂+u₁*e₂)+e₁*u₂) (e₁*e₂)
          linarith
      _ ≤ (|u₁*u₂|+|u₁*e₂|)+|e₁*u₂|+|e₁*e₂| := by
          gcongr; exact abs_add_le _ _
      _ ≤ tau+4*eps+eps^2 := by linarith
  have hsq : eps^2 ≤ eps := by nlinarith
  nlinarith

lemma expanded_parameterCell_mem_intercept {z tau gamma eps : ℝ} {s e : Plane}
    (hz : |z| ≤ 1) (hs : s ∈ parameterCell tau)
    (he₁ : |e.1| ≤ eps) (he₂ : |e.2| ≤ eps)
    (heps : eps < 1/2) (hgap : eps < gamma*tau/5) :
    ((1+z)*s.1+e.1, (1-z)*s.2+e.2) ∈ interceptCell tau gamma := by
  rcases opposite_expansion_bounds hz hs.1 hs.2.1 hs.2.2 with ⟨h₁,h₂,h₃⟩
  exact perturbed_product_bounds h₁ h₂ h₃ he₁ he₂ heps hgap

lemma quadrant_integral (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    (∫ _ in (0:ℝ)..(B/A), A) + (∫ x in (B/A)..A, B/x) =
      B*(1+Real.log (A^2/B)) := by
  have hBA : 0 < B/A := div_pos hB hA
  have hquot : A/(B/A) = A^2/B := by field_simp
  have hf : (fun x : ℝ => B/x) = (fun x : ℝ => B*x⁻¹) := by
    ext x; exact div_eq_mul_inv B x
  rw [hf, intervalIntegral.integral_const_mul, integral_inv_of_pos hBA hA,
    intervalIntegral.integral_const, hquot]
  simp only [sub_zero,smul_eq_mul]
  field_simp

lemma areaRatio_exp (gamma t : ℝ) (hg : 0 < 1+gamma) (ht : 0 ≤ t) :
    areaRatio (Real.exp (-t)) gamma =
      (1+gamma) + (1+gamma)*Real.log (9/(1+gamma))/(1+t) := by
  have hc : 1+gamma ≠ 0 := ne_of_gt hg
  have hlog₁ : Real.log (1 / Real.exp (-t)) = t := by
    rw [Real.log_div (by norm_num) (Real.exp_ne_zero _), Real.log_one, Real.log_exp]
    ring
  have hlog₂ : Real.log (9/((1+gamma)*Real.exp (-t))) =
      Real.log (9/(1+gamma))+t := by
    rw [Real.log_div (by norm_num) (mul_ne_zero hc (Real.exp_ne_zero _)),
      Real.log_mul hc (Real.exp_ne_zero _), Real.log_exp,
      Real.log_div (by norm_num) hc]
    ring
  unfold areaRatio
  rw [hlog₁,hlog₂]
  have hden : 1+t ≠ 0 := by linarith
  field_simp
  ring

lemma areaRatio_exp_tendsto (gamma : ℝ) (hg : 0 < 1+gamma) :
    Tendsto (fun t : ℝ => areaRatio (Real.exp (-t)) gamma)
      atTop (𝓝 (1+gamma)) := by
  have hinv : Tendsto (fun t : ℝ => (1+t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
  have hlim : Tendsto (fun t : ℝ =>
      (1+gamma)+(1+gamma)*Real.log (9/(1+gamma))/(1+t))
      atTop (𝓝 (1+gamma)) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv))
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  exact (areaRatio_exp gamma t hg ht).symm

lemma areaRatio_tendsto_zero (gamma : ℝ) (hg : 0 ≤ gamma) :
    Tendsto (fun tau : ℝ => areaRatio tau gamma) (𝓝[>] 0) (𝓝 (1+gamma)) := by
  have hc : 0 < 1+gamma := by linarith
  have hlog : Tendsto (fun tau : ℝ => -(Real.log tau)) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hlim := (areaRatio_exp_tendsto gamma hc).comp hlog
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with tau htau
  simp only [Function.comp_apply,neg_neg,Real.exp_log htau]

lemma exists_parameter_after_padding {gamma eta : ℝ}
    (hg : 0 ≤ gamma) (hge : gamma < eta) :
    ∃ tau : ℝ, 0 < tau ∧ tau < 1 ∧ (1+gamma)*tau < 1 ∧
      areaRatio tau gamma < 1+eta := by
  have hc : 0 < 1+gamma := by linarith
  have hr := (areaRatio_exp_tendsto gamma hc).eventually_lt_const (by linarith : 1+gamma < 1+eta)
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.eventually_lt_const
    (show (0:ℝ) < 1 by norm_num)
  have hp : Tendsto (fun t:ℝ => (1+gamma)*Real.exp (-t)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul Real.tendsto_exp_neg_atTop_nhds_zero
  have hpt := hp.eventually_lt_const (show (0:ℝ) < 1 by norm_num)
  obtain ⟨t,ht, hpt,hr⟩ := (ht.and (hpt.and hr)).exists
  exact ⟨Real.exp (-t), Real.exp_pos _, ht,hpt,hr⟩

lemma areaRatio_continuousAt_padding_zero (tau : ℝ) (htau : 0 < tau) :
    ContinuousAt (areaRatio tau) 0 := by
  unfold areaRatio
  have hn : (1+(0:ℝ))*tau ≠ 0 := by positivity
  have hn' : (9:ℝ)/((1+(0:ℝ))*tau) ≠ 0 := div_ne_zero (by norm_num) hn
  apply ContinuousAt.div_const
  apply ContinuousAt.mul
  · fun_prop
  · apply ContinuousAt.const_add
    have hd : ContinuousAt (fun gamma : ℝ => (9:ℝ)/((1+gamma)*tau)) 0 := by
      apply ContinuousAt.div
      · exact continuousAt_const
      · fun_prop
      · exact hn
    exact hd.log hn'

lemma exists_padding_after_parameter {tau eta : ℝ}
    (htau : 0 < tau) (htau1 : tau < 1)
    (hr : areaRatio tau 0 < 1+eta) :
    ∃ gamma : ℝ, 0 < gamma ∧ (1+gamma)*tau < 1 ∧
      areaRatio tau gamma < 1+eta := by
  have hR := (areaRatio_continuousAt_padding_zero tau htau).tendsto.eventually_lt_const hr
  have hP : Tendsto (fun gamma:ℝ => (1+gamma)*tau) (𝓝 0) (𝓝 tau) := by
    have hc : ContinuousAt (fun gamma : ℝ => (1+gamma)*tau) 0 := by fun_prop
    simpa using hc.tendsto
  have hP' := hP.eventually_lt_const htau1
  have hboth : ∀ᶠ gamma in 𝓝[>] (0:ℝ),
      (1+gamma)*tau < 1 ∧ areaRatio tau gamma < 1+eta :=
    (hP'.and hR).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ gamma in 𝓝[>] (0:ℝ), 0 < gamma := self_mem_nhdsWithin
  obtain ⟨gamma,hgamma,hrest⟩ := (hpos.and hboth).exists
  exact ⟨gamma,hgamma,hrest⟩

lemma exists_logarithmic_parameters {eta : ℝ} (heta : 0 < eta) :
    ∃ m : ℝ, 1 < m ∧ ∃ gamma : ℝ, 0 < gamma ∧
      (1+gamma)*(1/m^2) < 1 ∧ areaRatio (1/m^2) gamma < 1+eta := by
  obtain ⟨tau,htau,htau1,_,hr⟩ :=
    exists_parameter_after_padding (gamma:=0) (by norm_num) heta
  obtain ⟨gamma,hgamma,hpad,hratio⟩ := exists_padding_after_parameter htau htau1 hr
  have hsqrt : 0 < Real.sqrt tau := Real.sqrt_pos.2 htau
  have hsqrt1 : Real.sqrt tau < 1 := by
    nlinarith [Real.sq_sqrt htau.le, Real.sqrt_nonneg tau]
  have hm : 1 < 1/Real.sqrt tau := (lt_div_iff₀ hsqrt).mpr (by simpa using hsqrt1)
  have ht : 1/(1/Real.sqrt tau)^2 = tau := by
    calc 1/(1/Real.sqrt tau)^2 = (Real.sqrt tau)^2 := by field_simp
         _ = tau := Real.sq_sqrt htau.le
  refine ⟨1/Real.sqrt tau,hm,gamma,hgamma,?_,?_⟩
  · simpa only [ht] using hpad
  · simpa only [ht] using hratio

end ProductCells

end

end OAI
