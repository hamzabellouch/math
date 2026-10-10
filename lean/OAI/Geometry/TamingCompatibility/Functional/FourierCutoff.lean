import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction
namespace TamingCompatibility.CompactKernel

variable {K H F : Type*} [MetricSpace K]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def evaluate (k : K →ᵇ (H →L[ℂ] F)) (u : H) : K →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => k x u)
    (k.continuous.clm_apply continuous_const) (‖k‖ * ‖u‖)
    (fun x => (k x).le_opNorm u |>.trans
      (mul_le_mul_of_nonneg_right (k.norm_coe_le_norm x) (norm_nonneg u)))

lemma evaluate_apply (k : K →ᵇ (H →L[ℂ] F)) (u : H) (x : K) :
    evaluate k u x = k x u := rfl

lemma norm_evaluate_le (k : K →ᵇ (H →L[ℂ] F)) (u : H) :
    ‖evaluate k u‖ ≤ ‖k‖ * ‖u‖ := by
  apply (BoundedContinuousFunction.norm_le (f := evaluate k u)
    (mul_nonneg (norm_nonneg k) (norm_nonneg u))).mpr
  intro x
  exact ((k x).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (k.norm_coe_le_norm x) (norm_nonneg u))

def operator (k : K →ᵇ (H →L[ℂ] F)) : H →L[ℂ] (K →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := evaluate k
      map_add' := fun u v => by ext x; exact (k x).map_add u v
      map_smul' := fun c u => by ext x; exact (k x).map_smul c u }
    ‖k‖ (norm_evaluate_le k)

lemma operator_apply (k : K →ᵇ (H →L[ℂ] F)) (u : H) (x : K) :
    operator k u x = k x u := rfl

theorem compact_operator [CompactSpace K] [ProperSpace F]
    (k : K →ᵇ (H →L[ℂ] F)) : IsCompactOperator (operator k) := by
  apply (isCompactOperator_iff_isCompact_closure_image_ball (operator k).toLinearMap
    (show (0:ℝ) < 1 by norm_num)).mpr
  apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0:F) ‖k‖)
    (isCompact_closedBall _ _)
  · intro f x hf
    obtain ⟨u, hu, rfl⟩ := hf
    rw [Metric.mem_closedBall, dist_zero_right]
    have hu' : ‖u‖ ≤ 1 := (by simpa using hu : ‖u‖ < 1).le
    exact ((k x).le_opNorm u).trans
      ((mul_le_mul_of_nonneg_left hu' (norm_nonneg _)).trans
        (by simpa using k.norm_coe_le_norm x))
  · intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ,hδ,hk⟩ := Metric.continuousAt_iff.mp k.continuous.continuousAt ε hε
    refine ⟨δ,hδ,?_⟩
    intro y hy f
    obtain ⟨u,hu,hfu⟩ := f.2
    have hnu : ‖u‖ ≤ 1 := (by simpa using hu : ‖u‖ < 1).le
    rw [dist_comm]
    change dist (f.val y) (f.val x) < ε
    rw [← hfu]
    change dist (k y u) (k x u) < ε
    calc
      dist (k y u) (k x u) = ‖(k y - k x) u‖ := by rw [dist_eq_norm]; rfl
      _ ≤ ‖k y - k x‖ * ‖u‖ := (k y - k x).le_opNorm u
      _ ≤ ‖k y - k x‖ := by nlinarith [norm_nonneg (k y - k x)]
      _ < ε := by simpa only [dist_eq_norm] using hk hy

end TamingCompatibility.CompactKernel

open MeasureTheory FourierTransform
open scoped BoundedContinuousFunction RealInnerProductSpace ENNReal

namespace TamingCompatibility.FourierCutoff

lemma fourierChar_sub_bound (a b : ℝ) :
    ‖(Real.fourierChar a : ℂ) - (Real.fourierChar b : ℂ)‖ ≤
      2 * Real.pi * ‖a-b‖ := by
  have heq : (Real.fourierChar a : ℂ) - (Real.fourierChar b : ℂ) =
      ((Real.fourierChar (a-b) : ℂ)-1) * (Real.fourierChar b : ℂ) := by
    rw [sub_mul, one_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, sub_add_cancel]
  rw [heq, norm_mul, Circle.norm_coe, mul_one, Real.fourierChar_apply]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (a-b))
  rw [mul_comm (((2 * Real.pi * (a-b)) : ℝ) : ℂ) Complex.I]
  refine h.trans_eq ?_
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (by positivity)]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma phase_sub_bound (x y ξ : E) :
    ‖(Real.fourierChar ⟪ξ,x⟫ : ℂ) - (Real.fourierChar ⟪ξ,y⟫ : ℂ)‖ ≤
      (2 * Real.pi * ‖ξ‖) * ‖x-y‖ := by
  refine (fourierChar_sub_bound _ _).trans ?_
  rw [← inner_sub_right]
  have h := norm_inner_le_norm (𝕜 := ℝ) ξ (x-y)
  calc
    2 * Real.pi * ‖⟪ξ,x-y⟫‖ ≤ 2 * Real.pi * (‖ξ‖ * ‖x-y‖) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

def phase (x : E) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun ξ => (Real.fourierChar ⟪ξ,x⟫ : ℂ))
    (by fun_prop) 1 (fun ξ => le_of_eq (Circle.norm_coe (Real.fourierChar ⟪ξ,x⟫)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma phase_norm_le (x : E) : ‖phase x‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le (f := phase x) zero_le_one).mpr
  intro ξ
  change ‖(Real.fourierChar ⟪ξ,x⟫ : ℂ)‖ ≤ 1
  exact (Circle.norm_coe (Real.fourierChar ⟪ξ,x⟫)).le

def modulate (g : Lp ℂ 2 (volume : Measure E)) (x : E) : Lp ℂ 2 (volume : Measure E) :=
  ((phase x).memLp_top (μ := volume)).toLp _ • g

lemma modulate_coe (g : Lp ℂ 2 (volume : Measure E)) (x : E) :
    modulate g x =ᵐ[volume] fun ξ => (Real.fourierChar ⟪ξ,x⟫ : ℂ) * g ξ := by
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (((phase x).memLp_top (μ := volume)).toLp _) g,
    ((phase x).memLp_top (μ := volume)).coeFn_toLp] with ξ h1 h2
  change modulate g x ξ = (((phase x).memLp_top (μ := volume)).toLp _) ξ * g ξ at h1
  rw [h1, h2]
  rfl

lemma modulate_norm_le (g : Lp ℂ 2 (volume : Measure E)) (x : E) :
    ‖modulate g x‖ ≤ ‖g‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [modulate_coe g x] with ξ hξ
  rw [hξ, norm_mul, Circle.norm_coe, one_mul]

lemma modulate_sub_norm_le (g : Lp ℂ 2 (volume : Measure E))
    {R : ℝ} (hg : ∀ᵐ ξ ∂volume, R < ‖ξ‖ → g ξ = 0) (x y : E) :
    ‖modulate g x - modulate g y‖ ≤ (2 * Real.pi * R * ‖x-y‖) * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (modulate g x) (modulate g y),
    modulate_coe g x, modulate_coe g y, hg] with ξ hs hx hy hξ
  rw [hs, Pi.sub_apply, hx, hy, ← sub_mul, norm_mul]
  by_cases h : R < ‖ξ‖
  · simp [hξ h]
  · have hb := phase_sub_bound x y ξ
    have hb' : (2 * Real.pi * ‖ξ‖) * ‖x-y‖ ≤ (2 * Real.pi * R) * ‖x-y‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_of_not_gt h) (by positivity)) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right (hb.trans hb') (norm_nonneg _)

lemma continuous_modulate (g : Lp ℂ 2 (volume : Measure E))
    {R : ℝ} (hR : 0 ≤ R) (hg : ∀ᵐ ξ ∂volume, R < ‖ξ‖ → g ξ = 0) :
    Continuous (modulate g) := by
  let C : NNReal := ⟨2 * Real.pi * R * ‖g‖, by positivity⟩
  apply (show LipschitzWith C (modulate g) from ?_).continuous
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  change ‖modulate g x - modulate g y‖ ≤ (2 * Real.pi * R * ‖g‖) * ‖x-y‖
  convert modulate_sub_norm_le g hg x y using 1
  ring

def multiply (g : Lp ℂ 2 (volume : Measure E)) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 1 (volume : Measure E) :=
  LinearMap.mkContinuous
    { toFun := fun u => g • u
      map_add' := fun u v => Lp.add_smul g u v
      map_smul' := fun c u => (Lp.smul_comm c g u).symm }
    ‖g‖ (fun u => Lp.norm_smul_le g u)

def pairing (g : Lp ℂ 2 (volume : Measure E)) : Lp F 2 (volume : Measure E) →L[ℂ] F :=
  (L1.integralCLM' ℂ) ∘L multiply g

lemma pairing_norm_le (g : Lp ℂ 2 (volume : Measure E)) (u : Lp F 2 (volume : Measure E)) :
    ‖pairing g u‖ ≤ ‖g‖ * ‖u‖ := by
  change ‖L1.integralCLM' ℂ (g • u)‖ ≤ _
  rw [← L1.integral_eq' ℂ]
  exact (L1.norm_integral_le _).trans (Lp.norm_smul_le g u)

def pairingCLM : Lp ℂ 2 (volume : Measure E) →L[ℂ] (Lp F 2 (volume : Measure E) →L[ℂ] F) :=
  LinearMap.mkContinuous
    { toFun := pairing
      map_add' := fun g h => by
        ext u
        change L1.integralCLM' ℂ ((g+h) • u) =
          L1.integralCLM' ℂ (g • u) + L1.integralCLM' ℂ (h • u)
        rw [Lp.smul_add, map_add]
      map_smul' := fun c g => by
        ext u
        change L1.integralCLM' ℂ ((c • g) • u) = c • L1.integralCLM' ℂ (g • u)
        rw [Lp.smul_assoc, map_smul] }
    1 (fun g => by
      rw [one_mul]
      exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (pairing_norm_le g))

end TamingCompatibility.FourierCutoff

end

end OAI
