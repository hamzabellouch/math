import OAI.Probability.InvariantIsing.Cavity.CavityLinearTiltMoment
import OAI.Probability.InvariantIsing.Cavity.CavityFactorBound
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

namespace OAI

/-! Uniform moments of the remaining linear cavity tilt. The estimate uses
only the one-replica exponential radial moment after the quadratic tilt. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Topology

namespace InvariantIsing

def cavityLinearMomentEnvelope (p : ℕ) (c r : ℝ) : ℝ :=
  Real.exp (2 * c + (2 * p + 2 * c + 1) * r)

lemma cavity_linear_logFactor_growth {d n : ℕ}
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin d)) (ε : Spin n) :
    |cavityLogFactor 0 L C y ε| ≤
      (cavityMatrixMass L + cavityMatrixMass C) * (1 + ‖y‖) := by
  have hy i : |y i| ≤ ‖y‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
  have hL := cavity_bilinear_abs_bound L y (fun j => spinValue (ε j))
    (norm_nonneg y) zero_le_one hy (fun j => (abs_spinValue (ε j)).le)
  have hC := cavity_spin_quadratic_abs_bound C ε
  have hz : cavityQuadratic (0 : Matrix (Fin d) (Fin d) ℝ) y = 0 := by
    simp [cavityQuadratic]
  simp only [mul_one] at hL
  simp only [cavityLogFactor, hz, zero_add]
  apply (abs_add_le _ _).trans
  nlinarith [cavityMatrixMass_nonneg L, cavityMatrixMass_nonneg C, norm_nonneg y,
    mul_nonneg (cavityMatrixMass_nonneg C) (norm_nonneg y)]

lemma cavity_linear_envelope_bounds (p : ℕ) {c r v : ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hv : |v| ≤ c * (1 + r)) :
    |v| ≤ c * cavityLinearMomentEnvelope p c r ∧
    Real.exp v ≤ cavityLinearMomentEnvelope p c r ∧
    Real.exp (-v) ≤ cavityLinearMomentEnvelope p c r ∧
    r^p * Real.exp v ≤ cavityLinearMomentEnvelope p c r ∧
    (r^p * Real.exp v)^2 ≤ cavityLinearMomentEnvelope p c r ∧
    Real.exp (-v)^2 ≤ cavityLinearMomentEnvelope p c r := by
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hve := abs_le.mp hv
  have hexp : Real.exp r ≤ cavityLinearMomentEnvelope p c r := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlin : |v| ≤ c * cavityLinearMomentEnvelope p c r :=
    hv.trans (mul_le_mul_of_nonneg_left (by simpa only [add_comm] using (Real.add_one_le_exp r).trans hexp) hc)
  have hev : Real.exp v ≤ cavityLinearMomentEnvelope p c r := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hneg : Real.exp (-v) ≤ cavityLinearMomentEnvelope p c r := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hprod : r^p * Real.exp v ≤ Real.exp ((p : ℝ) * r + v) := by
    have h := cavity_polynomial_exp_bound p 0 r hr
    simp only [zero_mul, Real.exp_zero, mul_one, add_zero] at h
    calc
      _ ≤ Real.exp ((p : ℝ) * r) * Real.exp v :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have hprod1 : r^p * Real.exp v ≤ cavityLinearMomentEnvelope p c r :=
    hprod.trans (Real.exp_le_exp.mpr (by nlinarith))
  have hprod2 : (r^p * Real.exp v)^2 ≤ cavityLinearMomentEnvelope p c r := by
    apply (pow_le_pow_left₀ (mul_nonneg (pow_nonneg hr p) (Real.exp_pos _).le) hprod 2).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hneg2 : Real.exp (-v)^2 ≤ cavityLinearMomentEnvelope p c r := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith
  exact ⟨hlin, hev, hneg, hprod1, hprod2, hneg2⟩

theorem cavity_linear_tilt_radial_moment {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (V R : X → ℝ)
    (hV : Measurable V) (hR : Measurable R) (p : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hR0 : ∀ x, 0 ≤ R x) (hv : ∀ x, |V x| ≤ c * (1 + R x))
    (hi : Integrable (fun x => cavityLinearMomentEnvelope p c (R x)) ν) :
    Integrable (fun x => Real.exp (V x)) ν ∧
    Integrable (fun x => R x ^ p) (ν.tilted V) ∧
    (∫ x, R x ^ p ∂ν.tilted V) ≤
      ∫ x, cavityLinearMomentEnvelope p c (R x) ∂ν := by
  have hb x := cavity_linear_envelope_bounds p hc (hR0 x) (hv x)
  have hiV : Integrable V ν := (hi.const_mul c).mono' hV.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact (hb x).1)
  have hie : Integrable (fun x => Real.exp (V x)) ν := hi.mono' hV.exp.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact (hb x).2.1)
  have hin : Integrable (fun x => Real.exp (-V x)) ν := hi.mono' hV.neg.exp.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact (hb x).2.2.1)
  have hif : Integrable (fun x => R x^p * Real.exp (V x)) ν :=
    hi.mono' ((hR.pow_const p).mul hV.exp).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (hR0 x) p) (Real.exp_pos _).le)]
        exact (hb x).2.2.2.1)
  have hif2 : Integrable (fun x => (R x^p * Real.exp (V x))^2) ν :=
    hi.mono' (((hR.pow_const p).mul hV.exp).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact (hb x).2.2.2.2.1)
  have hin2 : Integrable (fun x => Real.exp (-V x)^2) ν :=
    hi.mono' ((hV.neg.exp).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact (hb x).2.2.2.2.2)
  have hit : Integrable (fun x => R x^p) (ν.tilted V) := by
    rw [integrable_tilted_iff hie]
    simpa only [smul_eq_mul, mul_comm] using hif
  refine ⟨hie, hit, (cavity_linear_tilt_moment_bound ν V (fun x => R x^p) hiV hie hin
    (fun x => pow_nonneg (hR0 x) p) hif hif2 hin2).trans ?_⟩
  have ha := integral_mono hif2 hi (fun x => (hb x).2.2.2.2.1)
  have hn := integral_mono hin2 hi (fun x => (hb x).2.2.2.2.2)
  linarith

theorem cavity_linear_tilt_mean_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω X) [IsMarkovKernel κ]
    (V : Ω × X → ℝ) (R : X → ℝ) (hV : Measurable V) (hR : Measurable R)
    (p : ℕ) {c : ℝ} (hc : 0 ≤ c) (hR0 : ∀ x, 0 ≤ R x)
    (hv : ∀ ω x, |V (ω, x)| ≤ c * (1 + R x))
    (hi : Integrable (fun x => cavityLinearMomentEnvelope p c (R x)) (κ ∘ₘ P)) :
    (∀ᵐ ω ∂P, Integrable (fun x => Real.exp (V (ω, x))) (κ ω) ∧
      Integrable (fun x => R x^p) ((κ ω).tilted (fun x => V (ω, x)))) ∧
    Integrable (fun ω => ∫ x, R x^p ∂(κ ω).tilted (fun x => V (ω, x))) P ∧
    (∫ ω, ∫ x, R x^p ∂(κ ω).tilted (fun x => V (ω, x)) ∂P) ≤
      ∫ x, cavityLinearMomentEnvelope p c (R x) ∂(κ ∘ₘ P) := by
  have hia := Measure.ae_integrable_of_integrable_comp hi
  have hpoint := hia.mono fun ω hω => cavity_linear_tilt_radial_moment (κ ω)
    (fun x => V (ω, x)) R (hV.comp measurable_prodMk_left) hR p hc hR0 (hv ω) hω
  have hE : Integrable (fun ω => ∫ x, cavityLinearMomentEnvelope p c (R x) ∂κ ω) P := by
    have hn := Measure.integrable_integral_norm_of_integrable_comp hi
    simpa only [Real.norm_eq_abs, cavityLinearMomentEnvelope, abs_of_pos (Real.exp_pos _)] using hn
  have hm : Measurable (fun ω => ∫ x, R x^p ∂(κ ω).tilted (fun x => V (ω, x))) :=
    measurable_random_tilted_integral κ.measurable hV
      ((hR.comp measurable_snd).pow_const p)
  have hmi : Integrable (fun ω => ∫ x, R x^p ∂(κ ω).tilted (fun x => V (ω, x))) P :=
    hE.mono' hm.aestronglyMeasurable (hpoint.mono fun ω hω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => pow_nonneg (hR0 x) p)]
      exact hω.2.2)
  refine ⟨hpoint.mono (fun _ h => ⟨h.1, h.2.1⟩), hmi, ?_⟩
  calc
    _ ≤ ∫ ω, ∫ x, cavityLinearMomentEnvelope p c (R x) ∂κ ω ∂P :=
      integral_mono_ae hmi hE (hpoint.mono fun _ h => h.2.2)
    _ = _ := by
      rw [Measure.comp_eq_comp_const_apply] at hi ⊢
      simpa only [Kernel.const_apply] using (Kernel.integral_comp hi).symm

end InvariantIsing

end

end OAI
