import Mathlib
import OAI.Analysis.Conductivity.Variational.SmoothPrimitive

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def connectorRate (K z : ℝ) : ℝ :=
  1/2 + (5/2)*smoothTransition ((z-1)/K)

def connectorProfile (K z : ℝ) : ℝ :=
  exp (-(∫ t in (0 : ℝ)..z, connectorRate K t))

lemma connectorRate_smooth (K : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (connectorRate K) := by
  exact contDiff_const.add (contDiff_const.mul (smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const K)))

lemma connectorRate_bounds (K z : ℝ) : 1/2 ≤ connectorRate K z ∧ connectorRate K z ≤ 3 := by
  have h₁ := smoothTransition.nonneg ((z-1)/K)
  have h₂ := smoothTransition.le_one ((z-1)/K)
  constructor <;> dsimp [connectorRate] <;> linarith

lemma connectorRate_left {K z : ℝ} (hK : 0 < K) (hz : z ≤ 1) :
    connectorRate K z = 1/2 := by
  rw [connectorRate,smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hK.le)]
  ring
lemma connectorRate_right {K z : ℝ} (hK : 0 < K) (hz : K+1 ≤ z) :
    connectorRate K z = 3 := by
  rw [connectorRate,smoothTransition.one_of_one_le
    ((le_div_iff₀ hK).mpr (by linarith))]
  ring

lemma connectorRate_hasDerivAt (K z : ℝ) : HasDerivAt (connectorRate K)
    ((5/(2*K))*deriv smoothTransition ((z-1)/K)) z := by
  have h := ((smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
    ((z-1)/K)).hasDerivAt
  have hh := ((h.comp z (((hasDerivAt_id z).sub_const 1).div_const K)).const_mul (5/2)).const_add (1/2)
  have he : (5/2)*(deriv smoothTransition ((z-1)/K)*(1/K)) =
      (5/(2*K))*deriv smoothTransition ((z-1)/K) := by ring
  change HasDerivAt (fun w => 1/2+(5/2)*smoothTransition ((w-1)/K))
    ((5/(2*K))*deriv smoothTransition ((z-1)/K)) z
  exact hh.congr_deriv (g' := (5/(2*K))*deriv smoothTransition ((z-1)/K)) he

lemma connectorRate_derivative_bounds {M K : ℝ} (hM : 1 ≤ M) (hK : 20*M ≤ K)
    (hbound : ∀ x : ℝ, |deriv smoothTransition x| ≤ M) (z : ℝ) :
    0 ≤ deriv (connectorRate K) z ∧ deriv (connectorRate K) z ≤ 1/8 := by
  have hKp : 0 < K := by linarith
  rw [(connectorRate_hasDerivAt K z).deriv]
  have hn : 0 ≤ deriv smoothTransition ((z-1)/K) := smoothTransition.monotone.deriv_nonneg
  have hu : deriv smoothTransition ((z-1)/K) ≤ M :=
    (le_abs_self _).trans (hbound _)
  constructor
  · positivity
  · calc
      _ ≤ (5/(2*K))*M := mul_le_mul_of_nonneg_left hu (by positivity)
      _ ≤ 1/8 := by
        rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0 < 2*K)]
        linarith

lemma connectorProfile_pos (K z : ℝ) : 0 < connectorProfile K z := exp_pos _
lemma connectorProfile_smooth (K : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (connectorProfile K) := by
  let r : SmoothScalar ℝ := ⟨connectorRate K,connectorRate_smooth K⟩
  exact ((smoothScalar_contDiff (smoothPrimitive r)).neg).exp

lemma connectorProfile_hasDerivAt (K z : ℝ) : HasDerivAt (connectorProfile K)
    (-connectorRate K z*connectorProfile K z) z := by
  have hr := (connectorRate_smooth K).continuous
  have h := intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable 0 z)
    (hr.stronglyMeasurableAtFilter _ _) hr.continuousAt
  change HasDerivAt (fun w => exp (-(∫ t in (0:ℝ)..w, connectorRate K t)))
    (-connectorRate K z*connectorProfile K z) z
  exact h.neg.exp.congr_deriv (g' := -connectorRate K z*connectorProfile K z)
    (by simp only [connectorProfile,Pi.neg_apply]; ring)

lemma connectorProfile_second (K z : ℝ) :
    deriv (deriv (connectorProfile K)) z =
      ((connectorRate K z)^2-deriv (connectorRate K) z)*connectorProfile K z := by
  have he : deriv (connectorProfile K) = fun z => -connectorRate K z*connectorProfile K z :=
    funext fun z => (connectorProfile_hasDerivAt K z).deriv
  rw [he]
  have h := (((connectorRate_smooth K).differentiable (by simp) z).hasDerivAt.neg).mul
    (connectorProfile_hasDerivAt K z)
  simp only [Pi.mul_def,Pi.neg_def] at h
  rw [h.deriv]
  ring

def connectorAngular (K z : ℝ) : ℝ :=
  deriv (deriv (connectorProfile K)) z / connectorProfile K z

lemma connectorAngular_formula (K z : ℝ) : connectorAngular K z =
    (connectorRate K z)^2-deriv (connectorRate K) z := by
  rw [connectorAngular,connectorProfile_second,mul_div_cancel_right₀ _
    (connectorProfile_pos K z).ne']

lemma connectorAngular_bounds {M K : ℝ} (hM : 1 ≤ M) (hK : 20*M ≤ K)
    (hbound : ∀ x : ℝ, |deriv smoothTransition x| ≤ M) (z : ℝ) :
    1/8 ≤ connectorAngular K z ∧ connectorAngular K z ≤ 9 := by
  rw [connectorAngular_formula]
  obtain ⟨hl,hu⟩ := connectorRate_bounds K z
  obtain ⟨hdl,hdu⟩ := connectorRate_derivative_bounds hM hK hbound z
  constructor <;> nlinarith

lemma connectorProfile_zero (K : ℝ) : connectorProfile K 0 = 1 := by
  simp [connectorProfile]

lemma connector_integral_pos {K : ℝ} (hK : 0 < K) :
    0 < ∫ t in (0 : ℝ)..(K+2), connectorRate K t := by
  have hle : (K+2)/2 ≤ ∫ t in (0 : ℝ)..(K+2), connectorRate K t := by
    calc
      _ = ∫ _t in (0 : ℝ)..(K+2), (1/2 : ℝ) := by simp; ring
      _ ≤ _ := intervalIntegral.integral_mono_on (by linarith)
        (continuous_const.intervalIntegrable _ _)
        ((connectorRate_smooth K).continuous.intervalIntegrable _ _)
        (fun x _ => (connectorRate_bounds K x).1)
  linarith

lemma connectorProfile_le_one {K z : ℝ} (hz : 0 ≤ z) : connectorProfile K z ≤ 1 := by
  apply exp_le_one_iff.mpr
  have hn : 0 ≤ ∫ t in (0 : ℝ)..z, connectorRate K t :=
    intervalIntegral.integral_nonneg hz (fun t _ => le_trans (by norm_num) (connectorRate_bounds K t).1)
  exact neg_nonpos.mpr hn

end ScalarConductivity

end

end OAI
