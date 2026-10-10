import OAI.Geometry.IsometricImmersion.Pulses.PulseProfiles
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Order.Field

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem axisBump_derivative_bound_exists {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ∃ C : ℝ, ∀ t, ‖iteratedFDeriv ℝ k (axisBump a) t‖ ≤ C :=
  ((axisBump_contDiff a).continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).bounded_above_of_compact_support
    ((axisBump_hasCompactSupport ha).iteratedFDeriv k)

def axisBumpDerivativeBound (a : ℝ) (ha : 0 < a) (k : ℕ) : ℝ :=
  1 + |Classical.choose (axisBump_derivative_bound_exists ha k)|

theorem axisBumpDerivativeBound_pos {a : ℝ} (ha : 0 < a) (k : ℕ) :
    0 < axisBumpDerivativeBound a ha k := by
  unfold axisBumpDerivativeBound
  positivity

theorem axisBump_derivative_le {a : ℝ} (ha : 0 < a) (k : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (axisBump a) t‖ ≤ axisBumpDerivativeBound a ha k := by
  have hc := Classical.choose_spec (axisBump_derivative_bound_exists ha k) t
  have habs := le_abs_self (Classical.choose (axisBump_derivative_bound_exists ha k))
  unfold axisBumpDerivativeBound
  linarith

def xiCLM : Coord →L[ℝ] ℝ := ContinuousLinearMap.proj 0
def thetaCLM (q0 : ℝ) : Coord →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 1 + q0 • ContinuousLinearMap.proj 0

def pulseScaleBound (q0 delta : ℝ) : ℝ :=
  1 + ‖xiCLM‖ + |delta⁻¹| * ‖thetaCLM q0‖

theorem pulseScaleBound_pos (q0 delta : ℝ) : 0 < pulseScaleBound q0 delta := by
  unfold pulseScaleBound
  positivity

theorem pulseScaleBound_xi (q0 delta : ℝ) : ‖xiCLM‖ ≤ pulseScaleBound q0 delta := by
  have h := mul_nonneg (abs_nonneg delta⁻¹) (norm_nonneg (thetaCLM q0))
  unfold pulseScaleBound
  linarith

theorem pulseScaleBound_theta (q0 delta : ℝ) :
    |delta⁻¹| * ‖thetaCLM q0‖ ≤ pulseScaleBound q0 delta := by
  unfold pulseScaleBound
  linarith [norm_nonneg xiCLM]

theorem norm_scaled_theta_le (q0 delta : ℝ) {tau : ℝ} (ht : 0 ≤ tau) :
    ‖(tau / delta) • thetaCLM q0‖ ≤ tau * pulseScaleBound q0 delta := by
  rw [norm_smul, Real.norm_eq_abs, div_eq_mul_inv, abs_mul, abs_of_nonneg ht]
  calc
    _ = tau * (|delta⁻¹| * ‖thetaCLM q0‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pulseScaleBound_theta q0 delta) ht

theorem norm_scaled_xi_le (q0 delta : ℝ) {tau : ℝ} (ht : 0 ≤ tau) :
    ‖tau • xiCLM‖ ≤ tau * pulseScaleBound q0 delta := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  exact mul_le_mul_of_nonneg_left (pulseScaleBound_xi q0 delta) ht

theorem linear_comp_derivative_bound {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (L : Coord →L[ℝ] ℝ) (k : ℕ) (p : Coord) {C s : ℝ}
    (hC : 0 ≤ C) (hfC : ∀ t, ‖iteratedFDeriv ℝ k f t‖ ≤ C)
    (hL : ‖L‖ ≤ s) :
    ‖iteratedFDeriv ℝ k (f ∘ L) p‖ ≤ C * s ^ k := by
  rw [L.iteratedFDeriv_comp_right hf p (WithTop.coe_le_coe.mpr le_top)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f (L p)‖ * ∏ _ : Fin k, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ k f (L p)‖ * ‖L‖ ^ k := by simp
    _ ≤ C * s ^ k := mul_le_mul (hfC _) (pow_le_pow_left₀ (norm_nonneg L) hL k)
      (pow_nonneg (norm_nonneg L) k) hC

def derivativeConvolution (A B : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A i * B (k - i)

theorem derivativeConvolution_nonneg {A B : ℕ → ℝ}
    (hA : ∀ k, 0 ≤ A k) (hB : ∀ k, 0 ≤ B k) (k : ℕ) :
    0 ≤ derivativeConvolution A B k :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _))

theorem product_derivative_bound {f g : Coord → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {A B : ℕ → ℝ} (hA : ∀ k, 0 ≤ A k) (hB : ∀ k, 0 ≤ B k)
    {s : ℝ} (hs : 0 ≤ s)
    (hfa : ∀ k p, ‖iteratedFDeriv ℝ k f p‖ ≤ A k * s ^ k)
    (hgb : ∀ k p, ‖iteratedFDeriv ℝ k g p‖ ≤ B k * s ^ k) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (fun q => f q * g q) p‖ ≤ derivativeConvolution A B k * s ^ k := by
  refine (norm_iteratedFDeriv_mul_le hf hg p (WithTop.coe_le_coe.mpr le_top)).trans ?_
  rw [derivativeConvolution, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hpow : s ^ i * s ^ (k - i) = s ^ k := by
    rw [← pow_add, Nat.add_sub_of_le hik]
  calc
    _ ≤ (k.choose i : ℝ) * (A i * s ^ i) * (B (k - i) * s ^ (k - i)) :=
      mul_le_mul_of_nonneg
        (mul_le_mul_of_nonneg le_rfl (hfa i p) (Nat.cast_nonneg _)
          (mul_nonneg (hA i) (pow_nonneg hs i))) (hgb (k - i) p)
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
        (mul_nonneg (hB (k - i)) (pow_nonneg hs (k - i)))
    _ = ((k.choose i : ℝ) * A i * B (k - i)) * s ^ k := by
      rw [← hpow]
      ring

def pulseCore (q0 a delta tau : ℝ) (p : Coord) : ℝ :=
  axisBump a (xiCLM p) * axisBump (1 / 2) (((tau / delta) • thetaCLM q0) p) *
    Real.cos ((tau • xiCLM) p)

theorem pulseCore_contDiff (q0 a delta tau : ℝ) : ContDiff ℝ ∞ (pulseCore q0 a delta tau) :=
  (((axisBump_contDiff a).comp_continuousLinearMap).mul
    ((axisBump_contDiff (1 / 2)).comp_continuousLinearMap)).mul
      Real.contDiff_cos.comp_continuousLinearMap

def pulseCoreDerivativeBound (a : ℝ) (ha : 0 < a) : ℕ → ℝ :=
  derivativeConvolution
    (derivativeConvolution (axisBumpDerivativeBound a ha)
      (axisBumpDerivativeBound (1 / 2) (by norm_num))) (fun _ => 1)

theorem pulseCoreDerivativeBound_nonneg {a : ℝ} (ha : 0 < a) (k : ℕ) :
    0 ≤ pulseCoreDerivativeBound a ha k :=
  derivativeConvolution_nonneg
    (derivativeConvolution_nonneg (fun _ => (axisBumpDerivativeBound_pos ha _).le)
      (fun _ => (axisBumpDerivativeBound_pos (by norm_num : (0 : ℝ) < 1 / 2) _).le))
    (fun _ => zero_le_one) k

theorem pulseCore_derivative_le {a : ℝ} (ha : 0 < a) (q0 delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (pulseCore q0 a delta tau) p‖ ≤
      pulseCoreDerivativeBound a ha k * (tau * pulseScaleBound q0 delta) ^ k := by
  have ht0 : 0 ≤ tau := le_trans zero_le_one ht
  have hs : 0 ≤ tau * pulseScaleBound q0 delta :=
    mul_nonneg ht0 (pulseScaleBound_pos q0 delta).le
  have hxi : ‖xiCLM‖ ≤ tau * pulseScaleBound q0 delta :=
    (pulseScaleBound_xi q0 delta).trans
      (le_mul_of_one_le_left (pulseScaleBound_pos q0 delta).le ht)
  have hχ (j : ℕ) (p : Coord) :=
    linear_comp_derivative_bound (axisBump_contDiff a) xiCLM j p
      (axisBumpDerivativeBound_pos ha j).le (axisBump_derivative_le ha j) hxi
  have hφ (j : ℕ) (p : Coord) :=
    linear_comp_derivative_bound (axisBump_contDiff (1 / 2))
      ((tau / delta) • thetaCLM q0) j p
      (axisBumpDerivativeBound_pos (by norm_num : (0 : ℝ) < 1 / 2) j).le
      (axisBump_derivative_le (by norm_num : (0 : ℝ) < 1 / 2) j)
      (norm_scaled_theta_le q0 delta ht0)
  have hcos (j : ℕ) (p : Coord) :
      ‖iteratedFDeriv ℝ j (Real.cos ∘ (tau • xiCLM)) p‖ ≤
        1 * (tau * pulseScaleBound q0 delta) ^ j := by
    apply linear_comp_derivative_bound Real.contDiff_cos (tau • xiCLM) j p zero_le_one
    · intro t
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
        Real.abs_iteratedDeriv_cos_le_one j t
    · exact norm_scaled_xi_le q0 delta ht0
  have hχφ := product_derivative_bound
    (axisBump_contDiff a).comp_continuousLinearMap
    (axisBump_contDiff (1 / 2)).comp_continuousLinearMap
    (fun _ => (axisBumpDerivativeBound_pos ha _).le)
    (fun _ => (axisBumpDerivativeBound_pos (by norm_num : (0 : ℝ) < 1 / 2) _).le)
    hs hχ hφ
  exact product_derivative_bound
    ((axisBump_contDiff a).comp_continuousLinearMap.mul
      (axisBump_contDiff (1 / 2)).comp_continuousLinearMap)
    Real.contDiff_cos.comp_continuousLinearMap
    (derivativeConvolution_nonneg (fun _ => (axisBumpDerivativeBound_pos ha _).le)
      (fun _ => (axisBumpDerivativeBound_pos (by norm_num : (0 : ℝ) < 1 / 2) _).le))
    (fun _ => zero_le_one) hs hχφ hcos k p

def thetaTensor (q0 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  thetaCovector q0 i * thetaCovector q0 j

theorem pulseTensor_eq_core (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) :
    pulseTensor q0 a N delta tau = fun p =>
      (1 / tau ^ N) • (pulseCore q0 a delta tau p • thetaTensor q0) := by
  ext p i j
  simp only [pulseTensor, pulseScalar, pulseCore, shearCoordinates, thetaCLM, xiCLM,
    temporalCutoff, thetaTensor, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, Matrix.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have harg : tau / delta * (p 1 + q0 * p 0) = tau * (p 1 + q0 * p 0) / delta := by ring
  rw [harg]
  ring

def pulseDerivativeBound (q0 a : ℝ) (ha : 0 < a) (delta : ℝ) (k : ℕ) : ℝ :=
  ‖thetaTensor q0‖ * pulseCoreDerivativeBound a ha k * pulseScaleBound q0 delta ^ k

theorem pulseDerivativeBound_nonneg (q0 a : ℝ) (ha : 0 < a) (delta : ℝ) (k : ℕ) :
    0 ≤ pulseDerivativeBound q0 a ha delta k :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (pulseCoreDerivativeBound_nonneg ha k))
    (pow_nonneg (pulseScaleBound_pos q0 delta).le k)

theorem pulseTensor_derivative_le (q0 a : ℝ) (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (pulseTensor q0 a N delta tau) p‖ ≤
      pulseDerivativeBound q0 a ha delta k * tau ^ k / tau ^ N := by
  have ht0 : 0 < tau := lt_of_lt_of_le zero_lt_one ht
  let T : Fin 2 → Fin 2 → ℝ := thetaTensor q0
  let L := ContinuousLinearMap.toSpanSingleton ℝ T
  have hcore : ContDiff ℝ ∞ (pulseCore q0 a delta tau) := pulseCore_contDiff q0 a delta tau
  have hnorm := L.norm_iteratedFDeriv_comp_left hcore.contDiffAt
    (WithTop.coe_le_coe.mpr le_top) (n := k) (x := p)
  have hLnorm : ‖L‖ = ‖T‖ := ContinuousLinearMap.norm_toSpanSingleton (𝕜 := ℝ) T
  rw [hLnorm] at hnorm
  have hnorm' : ‖iteratedFDeriv ℝ k (L ∘ pulseCore q0 a delta tau) p‖ ≤
      ‖thetaTensor q0‖ * pulseCoreDerivativeBound a ha k * (tau * pulseScaleBound q0 delta) ^ k := by
    refine hnorm.trans ?_
    exact (mul_le_mul_of_nonneg_left (pulseCore_derivative_le ha q0 delta ht k p)
      (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm
  rw [pulseTensor_eq_core]
  change ‖iteratedFDeriv ℝ k (fun q => (1 / tau ^ N) • (L ∘ pulseCore q0 a delta tau) q) p‖ ≤ _
  have hsmul :
      iteratedFDeriv ℝ k (fun q => (1 / tau ^ N : ℝ) • (L ∘ pulseCore q0 a delta tau) q) p =
        (1 / tau ^ N : ℝ) • iteratedFDeriv ℝ k (L ∘ pulseCore q0 a delta tau) p :=
    iteratedFDeriv_const_smul_apply' (i := k) (a := (1 / tau ^ N : ℝ))
      ((L.contDiff.comp hcore).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  rw [hsmul,
    norm_smul, Real.norm_of_nonneg (div_nonneg zero_le_one (pow_nonneg ht0.le N))]
  calc
    _ ≤ (1 / tau ^ N) *
        (‖thetaTensor q0‖ * pulseCoreDerivativeBound a ha k * (tau * pulseScaleBound q0 delta) ^ k) :=
      mul_le_mul_of_nonneg_left hnorm' (div_nonneg zero_le_one (pow_nonneg ht0.le N))
    _ = _ := by rw [mul_pow]; unfold pulseDerivativeBound; ring

theorem fixed_order_pulse_bound_tendsto_zero (q0 a : ℝ) (ha : 0 < a)
    (delta : ℝ) (N k : ℕ) (hk : k < N) :
    Tendsto (fun tau : ℝ => pulseDerivativeBound q0 a ha delta k * tau ^ k / tau ^ N)
      atTop (𝓝 0) := by
  have hd : N - k ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hk)
  have h := (tendsto_inv_atTop_zero : Tendsto (fun tau : ℝ => tau⁻¹) atTop (𝓝 0)).pow (N - k)
  have h' : Tendsto (fun tau : ℝ => pulseDerivativeBound q0 a ha delta k * (tau⁻¹) ^ (N - k))
      atTop (𝓝 0) := by
    simpa only [zero_pow hd, mul_zero] using h.const_mul (pulseDerivativeBound q0 a ha delta k)
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with tau ht
  have htne : tau ≠ 0 := ht.ne'
  have hN : N = k + (N - k) := (Nat.add_sub_of_le hk.le).symm
  have hratio : tau ^ k / tau ^ N = (tau⁻¹) ^ (N - k) := by
    conv_lhs => rw [hN, pow_add]
    rw [inv_pow]
    field_simp
  simp only [mul_div_assoc, hratio]

theorem supportedPulse_seminorm_le (q0 a : ℝ) (ha : 0 < a) (N : ℕ) (delta : ℝ)
    (hd : 0 < delta) {tau : ℝ} (ht : 1 ≤ tau)
    (hax : a ≤ 1 / 10) (hay : delta / (2 * tau) + |q0| * a ≤ 1 / 10) (k : ℕ) :
    perturbationSeminorm k
        (supportedPulse q0 a N delta tau ha hd (lt_of_lt_of_le zero_lt_one ht) hax hay) ≤
      pulseDerivativeBound q0 a ha delta k * tau ^ k / tau ^ N := by
  have ht0 : 0 ≤ tau := le_trans zero_le_one ht
  have hC : 0 ≤ pulseDerivativeBound q0 a ha delta k * tau ^ k / tau ^ N :=
    div_nonneg (mul_nonneg (pulseDerivativeBound_nonneg q0 a ha delta k) (pow_nonneg ht0 k))
      (pow_nonneg ht0 N)
  unfold perturbationSeminorm
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ hC k _).mpr
  intro p hp
  exact pulseTensor_derivative_le q0 a ha N delta ht k p

end SmoothLocal.Pulse

end

end OAI
