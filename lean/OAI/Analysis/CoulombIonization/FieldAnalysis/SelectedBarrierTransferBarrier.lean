import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierTransferBarrier
import OAI.Analysis.CoulombIonization.ThomasFermi.ScaledBarrierCorrectionBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma scaled_screened_field_eq {s : ℝ} (hs : 0 < s) (Z : ℝ)
    (μ : TFSpace → ℝ) (x : TFSpace) :
    s^4*(nuclearField Z (s • x)-tfPotential μ (s • x)) =
      nuclearField (s^3*Z) x-tfPotential (tfDilation s μ) x := by
  rw [mul_sub,nuclearField_dilation hs,tfPotential_dilation hs]

lemma scaled_barrier_eq {s : ℝ} (hs : 0 < s) (Z : ℝ)
    (a : TFSpace → ℝ) (x : TFSpace) :
    s^4*(nuclearField Z (s • x)+a (s • x)) =
      nuclearField (s^3*Z) x+s^4*a (s • x) := by
  rw [mul_add,nuclearField_dilation hs]

lemma scaled_barrier_lower {s r B Z : ℝ} (hs : 0 < s) {a : TFSpace → ℝ}
    (hlo : ∀ y, r ≤ ‖y‖ → outerBarrier B r y ≤ nuclearField Z y+a y) :
    ∀ x, r/s ≤ ‖x‖ → outerBarrier B (r/s) x ≤
      nuclearField (s^3*Z) x+s^4*a (s • x) := by
  intro x hx
  have hy : r ≤ ‖s • x‖ := by
    rw [norm_smul,Real.norm_of_nonneg hs.le]
    exact ((div_le_iff₀ hs).mp hx).trans_eq (mul_comm _ _)
  have ht := mul_le_mul_of_nonneg_left (hlo (s • x) hy) (pow_nonneg hs.le 4)
  rwa [outerBarrier_dilation hs,scaled_barrier_eq hs] at ht

lemma scaled_barrier_upper {s r C Z : ℝ} (hs : 0 < s) {a : TFSpace → ℝ}
    (hup : ∀ y, r ≤ ‖y‖ → nuclearField Z y+a y ≤ C/‖y‖^4) :
    ∀ x, r/s ≤ ‖x‖ → nuclearField (s^3*Z) x+s^4*a (s • x) ≤ C/‖x‖^4 := by
  intro x hx
  have hy : r ≤ ‖s • x‖ := by
    rw [norm_smul,Real.norm_of_nonneg hs.le]
    exact ((div_le_iff₀ hs).mp hx).trans_eq (mul_comm _ _)
  have ht := mul_le_mul_of_nonneg_left (hup (s • x) hy) (pow_nonneg hs.le 4)
  rw [scaled_barrier_eq hs] at ht
  have hh : s^4*(C/‖s • x‖^4) = C/‖x‖^4 := by
    rw [norm_smul,Real.norm_of_nonneg hs.le]
    field_simp
  exact ht.trans_eq hh

theorem selected_scaled_barrier_transfer_ball {a μ p : TFSpace → ℝ}
    {Z k r s l S M P c : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hl : 0 < l) (hS : 0 < S)
    (hal : 1/(2*l) ≤ r/s) (hk : 0 ≤ k) (hc : 0 ≤ c)
    (ha : Continuous a)
    (hμm : Measurable μ) (hμi : Integrable μ) (hM : 0 ≤ M)
    (hμn : ∀ x, 0 ≤ μ x) (hμb : ∀ x, μ x ≤ M)
    (hpm : Measurable p) (hpi : Integrable p) (hP : 0 ≤ P)
    (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ P)
    (hw : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource r μ p x+outerCoefficient r x*reaction k (nuclearField Z x+a x)))
    (hd : ∀ x : TFSpace, r/s ≤ ‖x‖ → ‖x‖ ≤ S →
      tfDilation s μ x ≤ k*(max (nuclearField (s^3*Z) x-tfPotential (tfDilation s μ) x-1) 0)^(3/2:ℝ)+
        l⁻¹^8/‖x‖^6)
    (hb : ∀ x : TFSpace, ‖x‖ = S → s^4*a (s • x)+tfPotential (tfDilation s μ) x ≤ c) :
    ∀ x ∈ closedBall (0:TFSpace) S,
      nuclearField (s^3*Z) x+s^4*a (s • x) ≤
      nuclearField (s^3*Z) x-tfPotential (tfDilation s μ) x+
        tfPotential (fun y => tfDilation s p y+annularApproximationError l (r/s) S y) x+c := by
  let q := annularApproximationError l (r/s) S
  have hqm : Measurable q := annularApproximationError_measurable _ _ _
  have hqn : ∀ x, 0 ≤ q x := annularApproximationError_nonneg _ _ _
  have hqb : ∀ x, q x ≤ 64*l⁻¹^2 := annularApproximationError_bound hl hal
  have hqi : Integrable q := (bounded_compact_mass_le hqm
    (by positivity : 0 ≤ 64*l⁻¹^2) hqn hqb (annularApproximationError_support _ _ _)).1
  apply barrier_transfer_ball (div_pos hr hs) hS (by norm_num : (0:ℝ) ≤ 1) hk hc
    ((ha.comp (continuous_id.const_smul s)).const_mul (s^4))
    (tfDilation_measurable hμm) (tfDilation_integrable hs hμi)
    (mul_nonneg (pow_nonneg hs.le 6) hM) (tfDilation_nonneg hμn)
    (fun x => mul_le_mul_of_nonneg_left (hμb _) (pow_nonneg hs.le 6))
    (tfDilation_measurable hpm) (tfDilation_integrable hs hpi)
    (mul_nonneg (pow_nonneg hs.le 6) hP) (tfDilation_nonneg hpn)
    (fun x => mul_le_mul_of_nonneg_left (hpb _) (pow_nonneg hs.le 6))
    hqm hqi (by positivity) hqn hqb (barrier_weak_dilation hs hw) _ hb
  intro x hx hxr
  have hxs : ‖x‖ ≤ S := (mem_ball_zero_iff.mp hx).le
  have hq : q x = l⁻¹^8/‖x‖^6 := by
    apply indicator_of_mem
    exact ⟨hxr,hxs⟩
  rw [hq,reaction]
  have hh := mul_le_mul_of_nonneg_left (hd x hxr hxs) (by positivity : (0:ℝ) ≤ 4*Real.pi)
  nlinarith only [hh]

end CoulombBarrier

end

end OAI
