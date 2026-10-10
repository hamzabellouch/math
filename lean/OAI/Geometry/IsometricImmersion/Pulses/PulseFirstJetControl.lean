import OAI.Geometry.IsometricImmersion.Curvature.CurvatureLowerTube
import OAI.Geometry.IsometricImmersion.Pulses.PulseDerivativeBounds
import OAI.Geometry.IsometricImmersion.Calculus.CoordinateJetNorm

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def scalarPulseDerivativeBound (a : ℝ) (ha : 0 < a) (delta : ℝ) (k : ℕ) : ℝ :=
  pulseCoreDerivativeBound a ha k * pulseScaleBound 0 delta ^ k

theorem scalarPulseDerivativeBound_nonneg {a : ℝ} (ha : 0 < a) (delta : ℝ) (k : ℕ) :
    0 ≤ scalarPulseDerivativeBound a ha delta k :=
  mul_nonneg (pulseCoreDerivativeBound_nonneg ha k) (pow_nonneg (pulseScaleBound_pos 0 delta).le k)

theorem pulseScalar_eq_core (a : ℝ) (N : ℕ) (delta tau : ℝ) :
    pulseScalar a N delta tau = fun p => (1/tau^N) • pulseCore 0 a delta tau p := by
  funext p
  simp only [pulseScalar,pulseCore,xiCLM,thetaCLM,temporalCutoff,
    add_apply,smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,zero_mul,add_zero]
  have ht : tau/delta*p 1 = tau*p 1/delta := by ring
  rw [ht]
  ring

theorem pulseScalar_derivative_le {a : ℝ} (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (k : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ k (pulseScalar a N delta tau) p‖ ≤
      scalarPulseDerivativeBound a ha delta k * tau^k/tau^N := by
  have ht0 : 0 < tau := zero_lt_one.trans_le ht
  rw [pulseScalar_eq_core]
  rw [iteratedFDeriv_const_smul_apply' (i := k) (a := (1/tau^N : ℝ))
    ((pulseCore_contDiff 0 a delta tau).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
    norm_smul,Real.norm_of_nonneg (div_nonneg zero_le_one (pow_nonneg ht0.le N))]
  calc
    _ ≤ (1/tau^N)*(pulseCoreDerivativeBound a ha k*(tau*pulseScaleBound 0 delta)^k) :=
      mul_le_mul_of_nonneg_left (pulseCore_derivative_le ha 0 delta ht k p)
        (div_nonneg zero_le_one (pow_nonneg ht0.le N))
    _ = _ := by rw [mul_pow]; unfold scalarPulseDerivativeBound; ring

def scalarPulseFirstJetBound (a : ℝ) (ha : 0 < a) (delta : ℝ) : ℝ :=
  max (scalarPulseDerivativeBound a ha delta 0) (scalarPulseDerivativeBound a ha delta 1)

theorem scalarPulseFirstJetBound_nonneg {a : ℝ} (ha : 0 < a) (delta : ℝ) :
    0 ≤ scalarPulseFirstJetBound a ha delta :=
  (scalarPulseDerivativeBound_nonneg ha delta 0).trans (le_max_left _ _)

def scalarPulseFirstJetBudget (a : ℝ) (ha : 0 < a) (N : ℕ) (delta tau : ℝ) : ℝ :=
  scalarPulseFirstJetBound a ha delta * tau/tau^N

theorem scalarPulseFirstJetBudget_nonneg {a : ℝ} (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) : 0 ≤ scalarPulseFirstJetBudget a ha N delta tau :=
  div_nonneg (mul_nonneg (scalarPulseFirstJetBound_nonneg ha delta) (zero_le_one.trans ht))
    (pow_nonneg (zero_le_one.trans ht) N)

theorem pulseScalar_first_jet_bounds {a : ℝ} (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (p : Coord) :
    |pulseScalar a N delta tau p| ≤ scalarPulseFirstJetBudget a ha N delta tau ∧
      ∀ i, |coordPartial i (pulseScalar a N delta tau) p| ≤ scalarPulseFirstJetBudget a ha N delta tau := by
  have ht0 : 0 ≤ tau := zero_le_one.trans ht
  have hden : 0 ≤ tau^N := pow_nonneg ht0 N
  have hB0 : scalarPulseDerivativeBound a ha delta 0 ≤ scalarPulseFirstJetBound a ha delta :=
    le_max_left _ _
  have hB1 : scalarPulseDerivativeBound a ha delta 1 ≤ scalarPulseFirstJetBound a ha delta :=
    le_max_right _ _
  constructor
  · have h := pulseScalar_derivative_le ha N delta ht 0 p
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,mul_one] at h
    exact h.trans (div_le_div_of_nonneg_right
      (hB0.trans (le_mul_of_one_le_right (scalarPulseFirstJetBound_nonneg ha delta) ht)) hden)
  · intro i
    have h := (norm_iteratedCoordPartial_le_jet
      (pulseScalar_contDiff a N delta tau).contDiffOn isOpen_univ [i] (mem_univ p)).trans
        (pulseScalar_derivative_le ha N delta ht 1 p)
    simp only [iteratedCoordPartial,Real.norm_eq_abs,pow_one] at h
    exact h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hB1 ht0) hden)

theorem thetaPulse_first_increment_bound {a : ℝ} (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 1 ≤ tau) (p : Coord) :
    ‖thetaCurvatureFirstIncrement (pulseScalar a N delta tau) p‖ ≤
      scalarPulseFirstJetBudget a ha N delta tau :=
  thetaCurvatureFirstIncrement_norm_le _ p (scalarPulseFirstJetBudget_nonneg ha N delta ht)
    (pulseScalar_first_jet_bounds ha N delta ht p).1 (pulseScalar_first_jet_bounds ha N delta ht p).2

theorem scalarPulseFirstJetBudget_tendsto_zero {a : ℝ} (ha : 0 < a) (N : ℕ)
    (hN : 1 < N) (delta : ℝ) :
    Tendsto (scalarPulseFirstJetBudget a ha N delta) atTop (𝓝 0) := by
  have hn : N-1 ≠ 0 := by omega
  have hi := (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).pow (N-1)
  have h : Tendsto (fun t : ℝ => scalarPulseFirstJetBound a ha delta*(t⁻¹)^(N-1)) atTop (𝓝 0) := by
    simpa only [zero_pow hn,mul_zero] using hi.const_mul (scalarPulseFirstJetBound a ha delta)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hN' : N = 1+(N-1) := by omega
  have hr : t/t^N = (t⁻¹)^(N-1) := by
    conv_lhs => rw [hN',pow_add,pow_one]
    rw [inv_pow]
    field_simp [ht.ne']
  simp only [scalarPulseFirstJetBudget,mul_div_assoc,hr]

theorem exists_uniform_actual_pulse_lower_bound (B : ℝ) {d : ℝ} (hd : 0 < d)
    {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, ∃ T : ℝ, 1 ≤ T ∧
      ∀ tau : ℝ, T ≤ tau → ∀ (g : MetricField) (p : Coord),
        ‖actualCurvatureFirstInput g p‖ ≤ B → d ≤ (g p).det →
        |thetaPulseLowerDifference g (pulseScalar a N delta tau) p| ≤
          C*scalarPulseFirstJetBudget a ha N delta tau := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_thetaPulseLowerDifference_bound B hd
  refine ⟨C,hC,?_⟩
  intro delta
  let beta := max B 0+1
  have hbeta : 0 < beta := by dsimp only [beta]; linarith [le_max_right B 0]
  let e := min 1 (d/(2*beta))
  have he : 0 < e := lt_min zero_lt_one (div_pos hd (mul_pos (by norm_num) hbeta))
  have hev : ∀ᶠ tau : ℝ in atTop, scalarPulseFirstJetBudget a ha N delta tau < e :=
    (scalarPulseFirstJetBudget_tendsto_zero ha N hN delta).eventually (eventually_lt_nhds he)
  obtain ⟨T,hT⟩ := eventually_atTop.mp hev
  refine ⟨max T 1,le_max_right _ _,?_⟩
  intro tau ht g p hg hdet
  have ht1 : 1 ≤ tau := (le_max_right _ _).trans ht
  have htT : T ≤ tau := (le_max_left _ _).trans ht
  have hsmall1 : scalarPulseFirstJetBudget a ha N delta tau ≤ 1 :=
    (hT tau htT).le.trans (min_le_left _ _)
  have hsmallD : scalarPulseFirstJetBudget a ha N delta tau ≤ d/(2*beta) :=
    (hT tau htT).le.trans (min_le_right _ _)
  have hg00 : |g p 0 0| ≤ beta := by
    have h0 : |g p 0 0| ≤ ‖actualCurvatureFirstInput g p‖ := by
      simpa only [Real.norm_eq_abs] using
        ((norm_le_pi_norm (g p 0) 0).trans (norm_le_pi_norm (g p) 0)).trans
          (norm_fst_le (actualCurvatureFirstInput g p))
    exact (h0.trans hg).trans (by dsimp only [beta]; linarith [le_max_left B 0])
  have hproduct : |g p 0 0| * |pulseScalar a N delta tau p| ≤ d/2 := by
    calc
      _ ≤ beta*scalarPulseFirstJetBudget a ha N delta tau :=
        mul_le_mul hg00 (pulseScalar_first_jet_bounds ha N delta ht1 p).1
          (abs_nonneg _) hbeta.le
      _ ≤ beta*(d/(2*beta)) := mul_le_mul_of_nonneg_left hsmallD hbeta.le
      _ = d/2 := by field_simp [hbeta.ne']
  have hinc := thetaPulse_first_increment_bound ha N delta ht1 p
  exact (hbound g (pulseScalar a N delta tau) p hg hdet (hinc.trans hsmall1) hproduct).trans
    (mul_le_mul_of_nonneg_left hinc hC)

end SmoothLocal.Pulse

end

end OAI
