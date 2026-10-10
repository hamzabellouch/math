import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarIntervalStability
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarReflection
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningScaledNorm

namespace OAI

/-! Compact-interval bounds for the scaled scalar Cauchy equation, used to
cross the fixed Airy interval uniformly in the original spectral parameters. -/

open Set
namespace DefocusingNLS

theorem spectralScalar_interval_norm_bound (a b B : ℝ) (hB : 0 ≤ B)
    (V : ℝ → ℂ) (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc a b))
    (hD : ∀ t ∈ Icc a b, HasDerivAt q (spectralScalarField (V t) (q t)) t)
    (hV : ∀ t ∈ Icc a b, ‖V t‖ ≤ B) (t : ℝ) (ht : t ∈ Icc a b) :
    ‖q t‖ ≤ ‖q a‖*Real.exp ((1+B)*(b-a)) := by
  have hh := spectralScalar_interval_stability a b B 0 0 hB (by norm_num) (by norm_num)
    V V q (fun _ => 0) hq continuousOn_const hD
    (fun t _ => by
      have hz : spectralScalarField (V t) (0 : ℂ × ℂ) = 0 := by
        ext <;> simp only [spectralScalarField,Prod.fst_zero,Prod.snd_zero,mul_zero]
      rw [hz]
      exact hasDerivAt_const t (0 : ℂ × ℂ))
    hV (by simp) (by simp) t ht
  simpa only [sub_zero,mul_zero,zero_div,add_zero] using hh

theorem spectralScalar_interval_norm_reverse (a b B : ℝ) (hab : a ≤ b) (hB : 0 ≤ B)
    (V : ℝ → ℂ) (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc a b))
    (hD : ∀ t ∈ Icc a b, HasDerivAt q (spectralScalarField (V t) (q t)) t)
    (hV : ∀ t ∈ Icc a b, ‖V t‖ ≤ B) :
    ‖q a‖ ≤ ‖q b‖*Real.exp ((1+B)*(b-a)) := by
  let j := fun t : ℝ => a+b-t
  have hj (t : ℝ) (ht : t ∈ Icc a b) : j t ∈ Icc a b := by
    dsimp only [j]
    constructor <;> linarith [ht.1,ht.2]
  let Q := spectralScalarReflect a b q
  have hQ : ContinuousOn Q (Icc a b) :=
    ((hq.comp (continuous_const.sub continuous_id).continuousOn hj).fst).prodMk
      ((hq.comp (continuous_const.sub continuous_id).continuousOn hj).snd.neg)
  have hQD (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt Q (spectralScalarField (V (j t)) (Q t)) t :=
    spectralScalarReflect_hasDerivAt a b t q (V (j t)) (hD (j t) (hj t ht))
  have hh := spectralScalar_interval_norm_bound a b B hB (fun t => V (j t)) Q hQ hQD
    (fun t ht => hV (j t) (hj t ht)) b ⟨hab,le_rfl⟩
  simpa only [Q,spectralScalarReflect,add_sub_cancel_right,add_sub_cancel_left,
    Prod.norm_def,norm_neg] using hh

theorem spectralShellNorm_le_norm (a b k : ℝ) (ha : 0 < a) (hak : a ≤ k) (hkb : k ≤ b)
    (u : ℂ × ℂ) : spectralShellNorm k u ≤ (b+a⁻¹)*‖u‖ := by
  have hk : 0 < k := ha.trans_le hak
  dsimp only [spectralShellNorm]
  have h₁ := mul_le_mul hkb (norm_fst_le u) (norm_nonneg _) (hk.le.trans hkb)
  have h₂ := mul_le_mul (inv_anti₀ ha hak) (norm_snd_le u) (norm_nonneg _) (inv_nonneg.mpr ha.le)
  nlinarith


theorem spectralScalar_interval_shell_bound (a b B low up ka kb : ℝ)
    (hab : a ≤ b) (hB : 0 ≤ B) (hlow : 0 < low)
    (hka : low ≤ ka) (hka' : ka ≤ up) (hkb : low ≤ kb) (hkb' : kb ≤ up)
    (V : ℝ → ℂ) (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc a b))
    (hD : ∀ t ∈ Icc a b, HasDerivAt q (spectralScalarField (V t) (q t)) t)
    (hV : ∀ t ∈ Icc a b, ‖V t‖ ≤ B) :
    let C := (up+low⁻¹)*max low⁻¹ up*Real.exp ((1+B)*(b-a))
    spectralShellNorm kb (q b) ≤ C*spectralShellNorm ka (q a) ∧
      spectralShellNorm ka (q a) ≤ C*spectralShellNorm kb (q b) := by
  have hup : 0 ≤ up := (hlow.le.trans hka).trans hka'
  have hc : 0 ≤ up+low⁻¹ := by positivity
  have hf := spectralScalar_interval_norm_bound a b B hB V q hq hD hV b ⟨hab,le_rfl⟩
  have hr := spectralScalar_interval_norm_reverse a b B hab hB V q hq hD hV
  constructor
  · calc
      _ ≤ (up+low⁻¹)*‖q b‖ := spectralShellNorm_le_norm low up kb hlow hkb hkb' _
      _ ≤ (up+low⁻¹)*(‖q a‖*Real.exp ((1+B)*(b-a))) := mul_le_mul_of_nonneg_left hf hc
      _ ≤ (up+low⁻¹)*((max low⁻¹ up*spectralShellNorm ka (q a))*Real.exp ((1+B)*(b-a))) := by
        gcongr
        exact spectralShellNorm_controls_norm low up ka hlow hka hka' _
      _ = _ := by ring
  · calc
      _ ≤ (up+low⁻¹)*‖q a‖ := spectralShellNorm_le_norm low up ka hlow hka hka' _
      _ ≤ (up+low⁻¹)*(‖q b‖*Real.exp ((1+B)*(b-a))) := mul_le_mul_of_nonneg_left hr hc
      _ ≤ (up+low⁻¹)*((max low⁻¹ up*spectralShellNorm kb (q b))*Real.exp ((1+B)*(b-a))) := by
        gcongr
        exact spectralShellNorm_controls_norm low up kb hlow hkb hkb' _
      _ = _ := by ring


theorem spectralScalar_interval_shell_subinterval (a b B low up : ℝ) (hab : a ≤ b)
    (hB : 0 ≤ B) (hlow : 0 < low) (V : ℝ → ℂ) (k : ℝ → ℝ) (q : ℝ → ℂ × ℂ)
    (hq : ContinuousOn q (Icc a b))
    (hD : ∀ t ∈ Icc a b, HasDerivAt q (spectralScalarField (V t) (q t)) t)
    (hV : ∀ t ∈ Icc a b, ‖V t‖ ≤ B)
    (hk : ∀ t ∈ Icc a b, low ≤ k t ∧ k t ≤ up)
    (r t : ℝ) (hr : r ∈ Icc a b) (ht : t ∈ Icc a b) (hrt : r ≤ t) :
    let C := (up+low⁻¹)*max low⁻¹ up*Real.exp ((1+B)*(b-a))
    spectralShellNorm (k t) (q t) ≤ C*spectralShellNorm (k r) (q r) ∧
      spectralShellNorm (k r) (q r) ≤ C*spectralShellNorm (k t) (q t) := by
  have hsub : Icc r t ⊆ Icc a b := Icc_subset_Icc hr.1 ht.2
  have hb := spectralScalar_interval_shell_bound r t B low up (k r) (k t) hrt hB hlow
    (hk r hr).1 (hk r hr).2 (hk t ht).1 (hk t ht).2 V q (hq.mono hsub)
    (fun s hs => hD s (hsub hs)) (fun s hs => hV s (hsub hs))
  have hup : 0 ≤ up := hlow.le.trans ((hk a ⟨le_rfl,hab⟩).1.trans (hk a ⟨le_rfl,hab⟩).2)
  have hNr := spectralShellNorm_nonneg (k r) (hlow.le.trans (hk r hr).1) (q r)
  have hNt := spectralShellNorm_nonneg (k t) (hlow.le.trans (hk t ht).1) (q t)
  constructor
  · exact hb.1.trans (by gcongr <;> linarith [hr.1,ht.2])
  · exact hb.2.trans (by gcongr <;> linarith [hr.1,ht.2])

end DefocusingNLS

end OAI
