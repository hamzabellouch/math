import OAI.Geometry.Perimeter.Regularity.EllipticLocality

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution
namespace RPISingularHarnack
open RPI.Boundary

def lineWindow (T : ℝ) : ℝ → ℝ := (Icc (-T) T).indicator (fun _ ↦ 1)

theorem lineWindow_measurable (T : ℝ) : Measurable (lineWindow T) :=
  measurable_const.indicator measurableSet_Icc

theorem lineWindow_integrable (T : ℝ) : Integrable (lineWindow T) volume :=
  continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem lineWindow_lintegral (T : ℝ) : (∫⁻ s : ℝ, ‖lineWindow T s‖ₑ) =
    ENNReal.ofReal (2*T) := by
  have he : (fun s ↦ ‖lineWindow T s‖ₑ) = (Icc (-T) T).indicator (fun _ ↦ (1:ℝ≥0∞)) := by
    funext s
    by_cases hs : s ∈ Icc (-T) T <;> simp [lineWindow,hs]
  rw [he,lintegral_indicator measurableSet_Icc]
  simp only [lintegral_const,Measure.restrict_apply_univ,one_mul,Real.volume_Icc]
  congr 1
  ring

theorem lineWindow_translation_le (T t : ℝ) :
    (∫⁻ s : ℝ, ‖lineWindow T (s-t)-lineWindow T s‖ₑ) ≤ ENNReal.ofReal (4*|t|) := by
  let J := Icc (-T-|t|) (-T+|t|)
  let K := Icc (T-|t|) (T+|t|)
  have hpoint (s : ℝ) : |lineWindow T (s-t)-lineWindow T s| ≤
      J.indicator (fun _ ↦ (1:ℝ)) s + K.indicator (fun _ ↦ (1:ℝ)) s := by
    have hJ0 : 0 ≤ J.indicator (fun _ ↦ (1:ℝ)) s := indicator_nonneg (fun _ _ ↦ zero_le_one) s
    have hK0 : 0 ≤ K.indicator (fun _ ↦ (1:ℝ)) s := indicator_nonneg (fun _ _ ↦ zero_le_one) s
    have hab := abs_nonneg t
    have htl := neg_abs_le t
    have htu := le_abs_self t
    by_cases h₁ : s-t ∈ Icc (-T) T
    · by_cases h₂ : s ∈ Icc (-T) T
      · simp only [lineWindow,indicator_of_mem h₁,indicator_of_mem h₂,sub_self,abs_zero]
        exact add_nonneg hJ0 hK0
      · have hjk : s ∈ J ∨ s ∈ K := by
          have h₁a := h₁.1
          have h₁b := h₁.2
          simp only [mem_Icc,not_and_or,not_le] at h₂
          rcases h₂ with h₂ | h₂
          · exact Or.inl ⟨by linarith,by linarith⟩
          · exact Or.inr ⟨by linarith,by linarith⟩
        simp only [lineWindow,indicator_of_mem h₁,indicator_of_notMem h₂,sub_zero,abs_one]
        rcases hjk with hj | hk
        · rw [indicator_of_mem hj]; linarith
        · rw [indicator_of_mem hk]; linarith
    · by_cases h₂ : s ∈ Icc (-T) T
      · have hjk : s ∈ J ∨ s ∈ K := by
          have h₂a := h₂.1
          have h₂b := h₂.2
          simp only [mem_Icc,not_and_or,not_le] at h₁
          rcases h₁ with h₁ | h₁
          · exact Or.inl ⟨by linarith,by linarith⟩
          · exact Or.inr ⟨by linarith,by linarith⟩
        simp only [lineWindow,indicator_of_notMem h₁,indicator_of_mem h₂,zero_sub,abs_neg,abs_one]
        rcases hjk with hj | hk
        · rw [indicator_of_mem hj]; linarith
        · rw [indicator_of_mem hk]; linarith
      · simp only [lineWindow,indicator_of_notMem h₁,indicator_of_notMem h₂,sub_self,abs_zero]
        exact add_nonneg hJ0 hK0
  have hd : Integrable (fun s ↦ lineWindow T (s-t)-lineWindow T s) volume :=
    ((lineWindow_integrable T).comp_sub_right t).sub (lineWindow_integrable T)
  have hJ : Integrable (J.indicator (fun _ ↦ (1:ℝ))) volume :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hK : Integrable (K.indicator (fun _ ↦ (1:ℝ))) volume :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  rw [← ofReal_integral_norm_eq_lintegral_enorm hd]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ s : ℝ, J.indicator (fun _ ↦ (1:ℝ)) s + K.indicator (fun _ ↦ (1:ℝ)) s :=
      integral_mono hd.norm (hJ.add hK) hpoint
    _ = 4*|t| := by
      rw [integral_add hJ hK,integral_indicator measurableSet_Icc,integral_indicator measurableSet_Icc]
      simp only [setIntegral_const,smul_eq_mul,mul_one,Measure.real,Real.volume_Icc]
      rw [show -T+|t|-(-T-|t|) = 2*|t| by ring,
        show T+|t|-(T-|t|) = 2*|t| by ring,ENNReal.toReal_ofReal (by positivity)]
      ring

def normalWindowAverage {n : ℕ} (v : Euc n) (T : ℝ) (f : Euc n → ℝ) (x : Euc n) : ℝ :=
  ∫ s : ℝ, lineWindow T s * f (x+s•v)

theorem normalWindowAverage_stronglyMeasurable {n : ℕ} {f : Euc n → ℝ}
    (hf : Measurable f) (v : Euc n) (T : ℝ) :
    StronglyMeasurable (normalWindowAverage v T f) := by
  apply StronglyMeasurable.integral_prod_right
  exact (((lineWindow_measurable T).comp measurable_snd).mul
    (hf.comp (continuous_fst.add (continuous_snd.smul continuous_const)).measurable)).stronglyMeasurable

theorem integrable_window_fiber {n : ℕ} {f : Euc n → ℝ} (hf : Measurable f)
    {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) (v : Euc n) (T : ℝ) (x : Euc n) :
    Integrable (fun s : ℝ ↦ lineWindow T s * f (x+s•v)) volume := by
  have hI : Integrable ((Icc (-T) T).indicator (fun _ ↦ C)) volume :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  apply hI.mono' (((lineWindow_measurable T).mul
    (hf.comp (continuous_const.add (continuous_id.smul continuous_const)).measurable)).aestronglyMeasurable)
  apply ae_of_all
  intro s
  by_cases hs : s ∈ Icc (-T) T
  · simpa [lineWindow,hs] using hb (x+s•v)
  · simp [lineWindow,hs]

theorem normalWindowAverage_lintegral_le {n : ℕ} {f : Euc n → ℝ}
    (hf : Measurable f) (v : Euc n) (T : ℝ) :
    (∫⁻ x, ‖normalWindowAverage v T f x‖ₑ) ≤
      ENNReal.ofReal (2*T) * ∫⁻ x, ‖f x‖ₑ := by
  have hm : Measurable (fun p : Euc n × ℝ ↦ ‖lineWindow T p.2‖ₑ * ‖f (p.1+p.2•v)‖ₑ) :=
    ((lineWindow_measurable T).comp measurable_snd).enorm.mul
      (hf.comp (continuous_fst.add (continuous_snd.smul continuous_const)).measurable).enorm
  calc
    _ ≤ ∫⁻ x, ∫⁻ s : ℝ, ‖lineWindow T s‖ₑ * ‖f (x+s•v)‖ₑ := by
      apply lintegral_mono
      intro x
      exact (enorm_integral_le_lintegral_enorm _).trans_eq
        (lintegral_congr (fun _ ↦ enorm_mul _ _))
    _ = ∫⁻ s : ℝ, ∫⁻ x, ‖lineWindow T s‖ₑ * ‖f (x+s•v)‖ₑ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      have he (s : ℝ) : (∫⁻ x, ‖lineWindow T s‖ₑ * ‖f (x+s•v)‖ₑ) =
          ‖lineWindow T s‖ₑ * ∫⁻ x, ‖f x‖ₑ := by
        rw [lintegral_const_mul _ (show Measurable (fun x : Euc n ↦ ‖f (x+s•v)‖ₑ) from
          (hf.comp (measurable_id.add measurable_const)).enorm)]
        rw [lintegral_add_right_eq_self (fun x : Euc n ↦ ‖f x‖ₑ)]
      simp_rw [he]
      rw [lintegral_mul_const _ (lineWindow_measurable T).enorm,lineWindow_lintegral]

theorem normalWindowAverage_translation_le {n : ℕ} {f : Euc n → ℝ}
    (hf : Measurable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C)
    (v : Euc n) (T : ℝ) (w : Euc n) :
    (∫⁻ x, ‖normalWindowAverage v T f (x+w)-normalWindowAverage v T f x‖ₑ) ≤
      ENNReal.ofReal (2*T) * ∫⁻ x, ‖f (x+w)-f x‖ₑ := by
  have he (x : Euc n) : normalWindowAverage v T f (x+w)-normalWindowAverage v T f x =
      normalWindowAverage v T (fun y ↦ f (y+w)-f y) x := by
    unfold normalWindowAverage
    rw [← integral_sub (integrable_window_fiber hf hb v T (x+w))
      (integrable_window_fiber hf hb v T x)]
    apply integral_congr_ae
    apply ae_of_all
    intro s
    have he : x+w+s•v = (x+s•v)+w := by abel
    simp only [he,mul_sub]
  simp_rw [he]
  exact normalWindowAverage_lintegral_le ((hf.comp (measurable_id.add measurable_const)).sub hf) v T

theorem normalWindowAverage_add_smul {n : ℕ} (v : Euc n) (T : ℝ)
    (f : Euc n → ℝ) (x : Euc n) (t : ℝ) :
    normalWindowAverage v T f (x+t•v) =
      ∫ s : ℝ, lineWindow T (s-t)*f (x+s•v) := by
  unfold normalWindowAverage
  have he : (fun s : ℝ ↦ lineWindow T (s-t)*f (x+s•v)) =
      (fun s : ℝ ↦ lineWindow T (s-t)*f (x+t•v+(s-t)•v)) := by
    funext s
    congr 2
    rw [sub_smul]
    abel
  rw [he]
  exact (integral_sub_right_eq_self (fun s : ℝ ↦ lineWindow T s*f (x+t•v+s•v)) t).symm

theorem normalWindowAverage_normal_translation_le {n : ℕ} {f : Euc n → ℝ}
    (hf : Measurable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C)
    (v : Euc n) (T t : ℝ) :
    (∫⁻ x, ‖normalWindowAverage v T f (x+t•v)-normalWindowAverage v T f x‖ₑ) ≤
      ENNReal.ofReal (4*|t|) * ∫⁻ x, ‖f x‖ₑ := by
  have hishift (x : Euc n) : Integrable (fun s : ℝ ↦ lineWindow T (s-t)*f (x+s•v)) volume := by
    have hi := (integrable_window_fiber hf hb v T (x+t•v)).comp_sub_right t
    convert hi using 1
    funext s
    congr 2
    rw [sub_smul]
    abel
  have he (x : Euc n) : normalWindowAverage v T f (x+t•v)-normalWindowAverage v T f x =
      ∫ s : ℝ, (lineWindow T (s-t)-lineWindow T s)*f (x+s•v) := by
    rw [normalWindowAverage_add_smul,normalWindowAverage,
      ← integral_sub (hishift x) (integrable_window_fiber hf hb v T x)]
    apply integral_congr_ae
    exact ae_of_all _ fun s ↦ (sub_mul _ _ _).symm
  let d : ℝ → ℝ := fun s ↦ lineWindow T (s-t)-lineWindow T s
  have hd : Measurable d := ((lineWindow_measurable T).comp
    (measurable_id.sub measurable_const)).sub (lineWindow_measurable T)
  have hm : Measurable (fun p : Euc n × ℝ ↦ ‖d p.2‖ₑ * ‖f (p.1+p.2•v)‖ₑ) :=
    (hd.comp measurable_snd).enorm.mul
      (hf.comp (continuous_fst.add (continuous_snd.smul continuous_const)).measurable).enorm
  calc
    _ ≤ ∫⁻ x, ∫⁻ s : ℝ, ‖d s‖ₑ * ‖f (x+s•v)‖ₑ := by
      apply lintegral_mono
      intro x
      change ‖normalWindowAverage v T f (x+t•v)-normalWindowAverage v T f x‖ₑ ≤ _
      rw [he]
      exact (enorm_integral_le_lintegral_enorm _).trans_eq
        (lintegral_congr (fun _ ↦ enorm_mul _ _))
    _ = ∫⁻ s : ℝ, ∫⁻ x, ‖d s‖ₑ * ‖f (x+s•v)‖ₑ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = (∫⁻ s : ℝ, ‖d s‖ₑ) * ∫⁻ x, ‖f x‖ₑ := by
      have he' (s : ℝ) : (∫⁻ x, ‖d s‖ₑ * ‖f (x+s•v)‖ₑ) =
          ‖d s‖ₑ * ∫⁻ x, ‖f x‖ₑ := by
        rw [lintegral_const_mul _ (show Measurable (fun x : Euc n ↦ ‖f (x+s•v)‖ₑ) from
          (hf.comp (measurable_id.add measurable_const)).enorm)]
        rw [lintegral_add_right_eq_self (fun x : Euc n ↦ ‖f x‖ₑ)]
      simp_rw [he']
      exact lintegral_mul_const _ hd.enorm
    _ ≤ _ := mul_le_mul_left (lineWindow_translation_le T t) _

theorem translation_lintegral_add_le {n : ℕ} {f : Euc n → ℝ}
    (hf : Measurable f) (a b : Euc n) :
    (∫⁻ x, ‖f (x+(a+b))-f x‖ₑ) ≤
      (∫⁻ x, ‖f (x+a)-f x‖ₑ) + ∫⁻ x, ‖f (x+b)-f x‖ₑ := by
  calc
    _ ≤ ∫⁻ x, ‖f ((x+b)+a)-f (x+b)‖ₑ + ‖f (x+b)-f x‖ₑ := by
      apply lintegral_mono
      intro x
      have he : f (x+(a+b))-f x =
          (f ((x+b)+a)-f (x+b)) + (f (x+b)-f x) := by
        abel_nf
      change ‖f (x+(a+b))-f x‖ₑ ≤ _
      rw [he]
      exact enorm_add_le _ _
    _ = _ := by
      rw [lintegral_add_left (show Measurable (fun x : Euc n ↦ ‖f ((x+b)+a)-f (x+b)‖ₑ) from
        ((hf.comp ((measurable_id.add measurable_const).add measurable_const)).sub
          (hf.comp (measurable_id.add measurable_const))).enorm)]
      rw [lintegral_add_right_eq_self (fun x : Euc n ↦ ‖f (x+a)-f x‖ₑ)]

theorem normalWindowAverage_all_translation_le {n : ℕ} {f : Euc n → ℝ}
    (hf : Measurable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C)
    {v : Euc n} (hv : ‖v‖ = 1) {T H V : ℝ}
    (hT : 0 ≤ T) (hH : 0 ≤ H) (hV : 0 ≤ V)
    (hmass : (∫⁻ x, ‖f x‖ₑ) ≤ ENNReal.ofReal V)
    (hhor : ∀ z, inner ℝ v z = 0 →
      (∫⁻ x, ‖f (x+z)-f x‖ₑ) ≤ ENNReal.ofReal (‖z‖*H))
    (w : Euc n) :
    (∫⁻ x, ‖normalWindowAverage v T f (x+w)-normalWindowAverage v T f x‖ₑ) ≤
      ENNReal.ofReal (‖w‖*(4*T*H+4*V)) := by
  let t : ℝ := inner ℝ v w
  let z : Euc n := w-t•v
  have ht : |t| ≤ ‖w‖ := by simpa only [hv,one_mul] using abs_real_inner_le_norm v w
  have hz : inner ℝ v z = 0 := by
    dsimp [z,t]
    rw [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hv]
    ring
  have hnz : ‖z‖ ≤ 2*‖w‖ := by
    calc
      _ ≤ ‖w‖ + ‖t•v‖ := norm_sub_le _ _
      _ = ‖w‖+|t| := by rw [norm_smul,Real.norm_eq_abs,hv,mul_one]
      _ ≤ _ := by linarith
  have he : w = z+t•v := by dsimp [z]; abel
  calc
    _ ≤ (∫⁻ x, ‖normalWindowAverage v T f (x+z)-normalWindowAverage v T f x‖ₑ) +
        ∫⁻ x, ‖normalWindowAverage v T f (x+t•v)-normalWindowAverage v T f x‖ₑ := by
      conv_lhs => rw [he]
      exact translation_lintegral_add_le (normalWindowAverage_stronglyMeasurable hf v T).measurable z (t•v)
    _ ≤ ENNReal.ofReal (2*T) * ENNReal.ofReal (‖z‖*H) +
        ENNReal.ofReal (4*|t|)*ENNReal.ofReal V := by
      exact add_le_add ((normalWindowAverage_translation_le hf hb v T z).trans
        (mul_le_mul_right (hhor z hz) _))
        ((normalWindowAverage_normal_translation_le hf hb v T t).trans
          (mul_le_mul_right hmass _))
    _ = ENNReal.ofReal ((2*T)*(‖z‖*H)+(4*|t|)*V) := by
      rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have h₁ : (2*T)*(‖z‖*H) ≤ (2*T)*(2*‖w‖*H) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnz hH) (by positivity)
      have h₂ : (4*|t|)*V ≤ (4*‖w‖)*V := by gcongr
      nlinarith

end RPISingularHarnack

end

end OAI
