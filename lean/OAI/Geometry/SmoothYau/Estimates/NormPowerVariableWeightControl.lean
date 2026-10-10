import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ThreeCoupledCleanChartJets

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples

lemma norm_power_variable_weight_control
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ 1 f) {φ : E → ℝ} (hφ : Continuous φ)
    {K : Set E} (hK : IsCompact K) :
    ∃ C>0, ∀ k : ℕ, 2≤k →
      ContDiff ℝ 1 (fun x => ‖f x‖^k) ∧
      ∀ x∈K, ‖fderiv ℝ (fun y => ‖f y‖^k) x‖ ≤
        C*productWaveFrequency k*(Real.exp (productWaveFrequency k*φ x)+‖f x‖^k) := by
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn (hf.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨R,hR⟩ := hK.exists_bound_of_continuousOn hφ.continuousOn
  let D := max R 0
  let B := max A 1
  let m := Real.exp (-2*D)
  have hB : 0<B := zero_lt_one.trans_le (le_max_right _ _)
  have hm : 0 < m := Real.exp_pos _
  refine ⟨B/m,div_pos hB hm,?_⟩
  intro k hk
  have hk1 : 1≤k := by omega
  have hkR : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hν := productWaveFrequency_bounds hk1
  have hν0 : 0≤productWaveFrequency k := (Nat.cast_nonneg _).trans hν.1
  have hfn : ContDiff ℝ 1 (fun x => ‖f x‖^k) := by
    simpa only [Real.rpow_natCast] using hf.norm_rpow hkR
  refine ⟨hfn,?_⟩
  intro x hx
  have hφlow : -D≤φ x := by
    have h := hR x hx
    rw [Real.norm_eq_abs] at h
    exact (neg_le_neg (le_max_left R 0)).trans ((neg_le_neg h).trans (neg_abs_le _))
  have hem : m^k≤Real.exp (productWaveFrequency k*φ x) := by
    dsimp [m]
    rw [←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonpos_right hν.2 (neg_nonpos.mpr (le_max_right R 0))
    have h2 := mul_le_mul_of_nonneg_left hφlow hν0
    dsimp [D] at *
    nlinarith
  let W := Real.exp (productWaveFrequency k*φ x)+‖f x‖^k
  have hpred : ‖f x‖^(k-1)≤W/m := by
    apply (le_div_iff₀ hm).mpr
    have hh := scalar_pred_power_weight_bound (norm_nonneg (f x)) hm (le_refl m) hk1
    have ht := hh.trans (add_le_add hem le_rfl)
    simpa only [W,mul_comm] using ht
  have hnorm : ‖fderiv ℝ (fun y => ‖f y‖^k) x‖ ≤ (k:ℝ)*‖f x‖^(k-1)*B := by
    have hh := norm_fderiv_norm_rpow_le (x:=x) (hf.differentiable one_ne_zero) hkR
    have hcast : (k:ℝ)-1=((k-1:ℕ):ℝ) := by rw [Nat.cast_sub hk1]; norm_num
    rw [hcast,Real.rpow_natCast] at hh
    simp only [Real.rpow_natCast] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left ((hA x hx).trans (le_max_left _ _)) (by positivity))
  calc
    _ ≤ (k:ℝ)*(W/m)*B := hnorm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpred (Nat.cast_nonneg _)) hB.le)
    _ ≤ productWaveFrequency k*(W/m)*B := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hν.1 (by dsimp [W]; positivity)) hB.le
    _ = _ := by dsimp [W]; ring

lemma two_power_variable_weight_control
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {K : Set E} (hK : IsCompact K) :
    ∃ T>0, ∃ H>0, ∀ k : ℕ, 2≤k →
      Differentiable ℝ (fun x => Real.exp (productWaveFrequency k*φ x)+‖a x‖^k+‖b x‖^k) ∧
      (∀ x, 0<Real.exp (productWaveFrequency k*φ x)+‖a x‖^k+‖b x‖^k) ∧
      (∀ x∈K, ∀ j≤2, ‖iteratedFDeriv ℝ j (fun y => (a y^k).re+(b y^k).re) x‖ ≤
        T*(productWaveFrequency k)^j*(Real.exp (productWaveFrequency k*φ x)+‖a x‖^k+‖b x‖^k)) ∧
      (∀ x∈K, ‖fderiv ℝ (fun y => Real.exp (productWaveFrequency k*φ y)+‖a y‖^k+‖b y‖^k) x‖ ≤
        H*productWaveFrequency k*(Real.exp (productWaveFrequency k*φ x)+‖a x‖^k+‖b x‖^k)) := by
  obtain ⟨A,hA,hAJ⟩ := real_power_variable_weighted_jets ha hK φ hφ.continuous.continuousOn 2
  obtain ⟨B,hB,hBJ⟩ := real_power_variable_weighted_jets hb hK φ hφ.continuous.continuousOn 2
  obtain ⟨C,hC,hCj⟩ := norm_power_variable_weight_control (ha.of_le (by simp)) hφ.continuous hK
  obtain ⟨D,hD,hDj⟩ := norm_power_variable_weight_control (hb.of_le (by simp)) hφ.continuous hK
  obtain ⟨H,hH,hHe⟩ := compact_exponential_envelope_log_bound hK hφ
  refine ⟨A+B,add_pos hA hB,H+C+D,by positivity,?_⟩
  intro k hk
  have hk1 : 1≤k := by omega
  have hν := productWaveFrequency_bounds hk1
  have hν0 : 0≤productWaveFrequency k := (Nat.cast_nonneg _).trans hν.1
  obtain ⟨hak,hakJ⟩ := hCj k hk
  obtain ⟨hbk,hbkJ⟩ := hDj k hk
  have he : ContDiff ℝ ∞ (fun x => Real.exp (productWaveFrequency k*φ x)) := (contDiff_const.mul hφ).exp
  have hWe : Differentiable ℝ (fun x => Real.exp (productWaveFrequency k*φ x)) := he.differentiable (by simp)
  refine ⟨(hWe.add (hak.differentiable one_ne_zero)).add (hbk.differentiable one_ne_zero),fun x => by positivity,?_,?_⟩
  · intro x hx j hj
    let W := Real.exp (productWaveFrequency k*φ x)+‖a x‖^k+‖b x‖^k
    have hwA : Real.exp (productWaveFrequency k*φ x)+‖a x‖^k≤W := le_add_of_nonneg_right (by positivity)
    have hwB : Real.exp (productWaveFrequency k*φ x)+‖b x‖^k≤W := by dsimp [W]; nlinarith [pow_nonneg (norm_nonneg (a x)) k]
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg k) hν.1 j
    have h1 := (hAJ k hk1 x hx j hj).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hpow hA.le) hwA (by positivity) (by positivity))
    have h2 := (hBJ k hk1 x hx j hj).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hpow hB.le) hwB (by positivity) (by positivity))
    exact (real_smooth_add_jet_bound (Complex.reCLM.contDiff.comp (ha.pow k))
      (Complex.reCLM.contDiff.comp (hb.pow k)) j x).trans (by
      change ‖iteratedFDeriv ℝ j (fun y => (a y^k).re) x‖+
        ‖iteratedFDeriv ℝ j (fun y => (b y^k).re) x‖ ≤ _
      calc
        _ ≤ A*(productWaveFrequency k)^j*W+B*(productWaveFrequency k)^j*W := add_le_add h1 h2
        _ = _ := by dsimp [W]; ring)
  · intro x hx
    have hea := hWe x
    have haa := hak.differentiable one_ne_zero x
    have hba := hbk.differentiable one_ne_zero x
    rw [fderiv_fun_add (hea.fun_add haa) hba,fderiv_fun_add hea haa]
    apply (norm_add_le _ _).trans
    apply (add_le_add (norm_add_le _ _) le_rfl).trans
    have h1 := hHe (productWaveFrequency k) hν0 x hx
    have h2 := hakJ x hx
    have h3 := hbkJ x hx
    calc
      _ ≤ H*productWaveFrequency k*Real.exp (productWaveFrequency k*φ x)+
          C*productWaveFrequency k*(Real.exp (productWaveFrequency k*φ x)+‖a x‖^k)+
          D*productWaveFrequency k*(Real.exp (productWaveFrequency k*φ x)+‖b x‖^k) := by linarith
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hH hν0) (pow_nonneg (norm_nonneg (a x)) k),
        mul_nonneg (mul_nonneg hH hν0) (pow_nonneg (norm_nonneg (b x)) k),
        mul_nonneg (mul_nonneg hC.le hν0) (pow_nonneg (norm_nonneg (b x)) k),
        mul_nonneg (mul_nonneg hD.le hν0) (pow_nonneg (norm_nonneg (a x)) k)]
end YauCounterexamples
end

end OAI
