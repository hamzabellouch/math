import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PeriodicHeatModes

namespace OAI

/-! Differentiation of the actual periodic heat Fourier series at positive
 times, with summable Gaussian majorants for its weighted moments. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff BigOperators

def periodicHeatMoment (k : ℕ) (p : ℝ × ℝ) : ℂ := ∑' n : ℤ, heatMode k n p

def periodicHeatMomentDerivative (k : ℕ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  ∑' n : ℤ, heatMode k n p • heatModeLinear n

theorem periodicHeatMoment_summable (k : ℕ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    Summable (fun n : ℤ => heatMode k n p) :=
  (heatModeBound_summable k hp).of_norm_bounded (fun n => (heatMode_norm k n p).le)

theorem periodicHeatMoment_hasFDerivAt (k : ℕ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    HasFDerivAt (periodicHeatMoment k) (periodicHeatMomentDerivative k p) p := by
  let T := p.1 / 2
  let V : Set (ℝ × ℝ) := Ioi T ×ˢ univ
  have hT : 0 < T := half_pos hp
  have hpV : p ∈ V := ⟨by change p.1 / 2 < p.1; linarith, mem_univ _⟩
  have hVo : IsOpen V := isOpen_Ioi.prod isOpen_univ
  have hVc : IsPreconnected V := ((convex_Ioi T).prod convex_univ).isPreconnected
  exact hasFDerivAt_tsum_of_isPreconnected (heatModeDerivativeBound_summable k hT)
    hVo hVc (fun n q _ => heatMode_hasFDerivAt k n q)
    (fun n q hq => heatMode_derivative_norm_le k n hq.1.le)
    hpV (periodicHeatMoment_summable k hp) hpV

theorem periodicHeatMoment_continuousOn (k : ℕ) :
    ContinuousOn (periodicHeatMoment k) (Ioi (0 : ℝ) ×ˢ univ) := by
  intro p hp
  exact (periodicHeatMoment_hasFDerivAt k hp.1).continuousAt.continuousWithinAt

theorem periodicHeatMomentDerivative_eq (k : ℕ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    periodicHeatMomentDerivative k p =
      (-4 * (Real.pi : ℂ) ^ 2 * periodicHeatMoment (k + 2) p) •
        (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
      (2 * (Real.pi : ℂ) * periodicHeatMoment (k + 1) p) •
        (Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ))) := by
  let A := Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let B := Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ))
  let c₀ : ℂ := -4 * (Real.pi : ℂ) ^ 2
  let c₁ : ℂ := 2 * (Real.pi : ℂ)
  have he (n : ℤ) : heatMode k n p • heatModeLinear n =
      (c₀ * heatMode (k + 2) n p) • A + (c₁ * heatMode (k + 1) n p) • B := by
    apply ContinuousLinearMap.ext
    intro q
    simp only [heatMode, heatModeLinear, A, B, c₀, c₁, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Complex.ofRealCLM_apply, Complex.real_smul, smul_eq_mul,
      pow_add, pow_two]
    push_cast
    ring
  have h₀ := periodicHeatMoment_summable (k + 2) hp
  have h₁ := periodicHeatMoment_summable (k + 1) hp
  unfold periodicHeatMomentDerivative
  simp_rw [he]
  rw [((h₀.mul_left c₀).smul_const A).tsum_add ((h₁.mul_left c₁).smul_const B),
    (h₀.mul_left c₀).tsum_smul_const, (h₁.mul_left c₁).tsum_smul_const,
    h₀.tsum_mul_left, h₁.tsum_mul_left]
  rfl

theorem periodicHeatMoment_contDiffOn_nat (m : ℕ) (k : ℕ) :
    ContDiffOn ℝ m (periodicHeatMoment k) (Ioi (0 : ℝ) ×ˢ univ) := by
  induction m generalizing k with
  | zero => exact contDiffOn_zero.mpr (periodicHeatMoment_continuousOn k)
  | succ m ih =>
    have ho : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
    have hd : DifferentiableOn ℝ (periodicHeatMoment k) (Ioi (0 : ℝ) ×ˢ univ) := by
      intro p hp
      exact (periodicHeatMoment_hasFDerivAt k hp.1).differentiableAt.differentiableWithinAt
    have hF : ContDiffOn ℝ m (fun p : ℝ × ℝ =>
        (-4 * (Real.pi : ℂ) ^ 2 * periodicHeatMoment (k + 2) p) •
          (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
        (2 * (Real.pi : ℂ) * periodicHeatMoment (k + 1) p) •
          (Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ))))
        (Ioi (0 : ℝ) ×ˢ univ) :=
      ((contDiffOn_const.mul (ih (k + 2))).smul contDiffOn_const).add
        ((contDiffOn_const.mul (ih (k + 1))).smul contDiffOn_const)
    have hfd : ContDiffOn ℝ m (fderiv ℝ (periodicHeatMoment k)) (Ioi (0 : ℝ) ×ˢ univ) := by
      apply hF.congr
      intro p hp
      rw [(periodicHeatMoment_hasFDerivAt k hp.1).fderiv,
        periodicHeatMomentDerivative_eq k hp.1]
    have hsucc := (contDiffOn_succ_iff_fderiv_of_isOpen ho).mpr
      ⟨hd, by simp, hfd⟩
    simpa only [Nat.cast_add, Nat.cast_one] using hsucc

theorem periodicHeatMoment_smooth (k : ℕ) :
    ContDiffOn ℝ ∞ (periodicHeatMoment k) (Ioi (0 : ℝ) ×ˢ univ) := by
  rw [contDiffOn_infty]
  intro m
  exact periodicHeatMoment_contDiffOn_nat m k

end ForcedComputation.VelocityDetector

end

end OAI
