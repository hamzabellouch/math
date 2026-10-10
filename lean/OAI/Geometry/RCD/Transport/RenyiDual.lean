import OAI.Geometry.RCD.Transport.RenyiDualScore

namespace OAI

/-! # The upper semicontinuous dual Rényi functional

All tests in the infimum are bounded and continuous. Measurable bounded
tests give the same upper bounds by simultaneous L¹ approximation for the
reference measure and the transported measure.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def scaledExpBCF (a : ℝ) (f : X →ᵇ ℝ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => Real.exp (a*f x))
    (Real.continuous_exp.comp (continuous_const.mul f.continuous))
    (Real.exp (|a| *‖f‖)) (fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      exact (le_abs_self _).trans ((abs_mul _ _).trans_le
        (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (abs_nonneg a))))

def renyiDualValue (μ ν : Measure X) (q : ℝ) (f : X → ℝ) : ℝ :=
  q*(∫ x, Real.exp ((q-1)*f x) ∂ν)+(1-q)*(∫ x, Real.exp (q*f x) ∂μ)

def renyiDual (μ ν : Measure X) (q : ℝ) : ℝ≥0∞ :=
  ⨅ f : X →ᵇ ℝ, ENNReal.ofReal (renyiDualValue μ ν q f)

theorem upperSemicontinuous_renyiDual (μ : Measure X) (q : ℝ) :
    UpperSemicontinuous (fun ν : ProbabilityMeasure X => renyiDual μ ν q) := by
  apply upperSemicontinuous_iInf
  intro f
  apply Continuous.upperSemicontinuous
  apply ENNReal.continuous_ofReal.comp
  change Continuous (fun ν : ProbabilityMeasure X => q*(∫ x, scaledExpBCF (q-1) f x ∂(ν : Measure X))+(1-q)*(∫ x, Real.exp (q*f x) ∂μ))
  exact (continuous_const.mul (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (scaledExpBCF (q-1) f))).add continuous_const

theorem scaled_exp_error {M a u v : ℝ} (hu : |u| ≤ M) (hv : |v| ≤ M) :
    |Real.exp (a*u)-Real.exp (a*v)| ≤
      (|a| *Real.exp (|a| *M))*|u-v| := by
  have hau : a*u ≤ |a| *M := (le_abs_self _).trans
    ((abs_mul _ _).trans_le (mul_le_mul_of_nonneg_left hu (abs_nonneg a)))
  have hav : a*v ≤ |a| *M := (le_abs_self _).trans
    ((abs_mul _ _).trans_le (mul_le_mul_of_nonneg_left hv (abs_nonneg a)))
  have h := exp_error_le hau hav
  rw [← mul_sub, abs_mul] at h
  calc
    _ ≤ Real.exp (|a| *M)*(|a| *|u-v|) := h
    _ = _ := by ring

omit [MetricSpace X] [BorelSpace X] in
theorem integral_scaled_exp_error (μ : Measure X) [IsFiniteMeasure μ]
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g) {M a : ℝ}
    (hfb : ∀ x, |f x| ≤ M) (hgb : ∀ x, |g x| ≤ M) :
    (∫ x, Real.exp (a*f x) ∂μ) ≤ (∫ x, Real.exp (a*g x) ∂μ)+
      (|a| *Real.exp (|a| *M))*(∫ x, |f x-g x| ∂μ) := by
  have hb (u : X → ℝ) (hu : ∀ x, |u x| ≤ M) (x : X) : a*u x ≤ |a| *M :=
    (le_abs_self _).trans ((abs_mul _ _).trans_le
      (mul_le_mul_of_nonneg_left (hu x) (abs_nonneg a)))
  have hif := bounded_exp_integrable μ (measurable_const.mul hf) (hb f hfb)
  have hig := bounded_exp_integrable μ (measurable_const.mul hg) (hb g hgb)
  change Integrable (fun x => Real.exp (a*f x)) μ at hif
  change Integrable (fun x => Real.exp (a*g x)) μ at hig
  have hiabs : Integrable (fun x => |f x-g x|) μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      ((bounded_measurable_integrable μ hf hfb).sub
        (bounded_measurable_integrable μ hg hgb)).norm
  have h := integral_mono hif (hig.add (hiabs.const_mul (|a| *Real.exp (|a| *M))))
    (fun x => by
      have hx := (le_abs_self (Real.exp (a*f x)-Real.exp (a*g x))).trans
        (scaled_exp_error (a := a) (hfb x) (hgb x))
      change Real.exp (a*f x) ≤ Real.exp (a*g x)+_
      linarith)
  change (∫ x, Real.exp (a*f x) ∂μ) ≤
    ∫ x, Real.exp (a*g x)+(|a| * Real.exp (|a| * M))*|f x-g x| ∂μ at h
  rw [integral_add hig (hiabs.const_mul _), integral_const_mul] at h
  exact h

omit [MetricSpace X] [BorelSpace X] in
theorem renyiDualValue_error (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g) {M ε : ℝ}
    (hfb : ∀ x, |f x| ≤ M) (hgb : ∀ x, |g x| ≤ M)
    (heμ : (∫ x, |f x-g x| ∂μ) ≤ ε) (heν : (∫ x, |f x-g x| ∂ν) ≤ ε) :
    renyiDualValue μ ν q f ≤ renyiDualValue μ ν q g+
      (q*(|q-1| *Real.exp (|q-1| *M))+(1-q)*(|q| *Real.exp (|q| *M)))*ε := by
  have hν := integral_scaled_exp_error ν (a := q-1) hf hg hfb hgb
  have hμ := integral_scaled_exp_error μ (a := q) hf hg hfb hgb
  have hbν := mul_le_mul_of_nonneg_left heν
    (show 0 ≤ |q-1| *Real.exp (|q-1| *M) by positivity)
  have hbμ := mul_le_mul_of_nonneg_left heμ
    (show 0 ≤ |q| *Real.exp (|q| *M) by positivity)
  have heν' : (∫ x, Real.exp ((q-1)*f x) ∂ν) ≤
      (∫ x, Real.exp ((q-1)*g x) ∂ν)+(|q-1| * Real.exp (|q-1| * M))*ε := by
    linarith
  have heμ' : (∫ x, Real.exp (q*f x) ∂μ) ≤
      (∫ x, Real.exp (q*g x) ∂μ)+(|q| * Real.exp (|q| * M))*ε := by
    linarith
  have hν' := mul_le_mul_of_nonneg_left heν' hq0
  have hμ' := mul_le_mul_of_nonneg_left heμ' (sub_nonneg.mpr hq1)
  dsimp [renyiDualValue]
  nlinarith only [hν',hμ']

theorem renyiDualValue_measurable_ge [ProperSpace X] [SeparableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {f : X → ℝ} (hf : Measurable f) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |f x| ≤ M) {b : ℝ}
    (h : ∀ g : X →ᵇ ℝ, b ≤ renyiDualValue μ ν q g) :
    b ≤ renyiDualValue μ ν q f := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let C := q*(|q-1| *Real.exp (|q-1| *M))+(1-q)*(|q| *Real.exp (|q| *M))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let δ := ε/(C+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hfi := bounded_measurable_integrable (μ+ν) hf hb
  obtain ⟨g,hg,_⟩ := hfi.exists_boundedContinuous_integral_sub_le hδ
  let u := clipBCF M hM g
  have hu := clipBCF_abs_le M hM g
  have hiμ := bounded_measurable_integrable μ hf hb
  have hiν := bounded_measurable_integrable ν hf hb
  have hsum := integral_add_measure (hiμ.sub (g.integrable μ)).norm
    (hiν.sub (g.integrable ν)).norm
  simp only [Pi.sub_apply] at hsum
  rw [hsum] at hg
  have hnμ : 0 ≤ ∫ x, ‖f x-g x‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  have hnν : 0 ≤ ∫ x, ‖f x-g x‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  have hbnd (ξ : Measure X) [IsFiniteMeasure ξ] (hi : Integrable f ξ)
      (hg' : (∫ x, ‖f x-g x‖ ∂ξ) ≤ δ) : (∫ x, |u x-f x| ∂ξ) ≤ δ := by
    have hh := integral_mono (hi.sub (u.integrable ξ)).norm
      (hi.sub (g.integrable ξ)).norm (fun x => clip_error_le M (f x) (g x) hM (hb x))
    simpa only [Real.norm_eq_abs, Pi.sub_apply, abs_sub_comm (f _) (u _)] using hh.trans hg'
  have heμ := hbnd μ hiμ (by linarith)
  have heν := hbnd ν hiν (by linarith)
  have herr := renyiDualValue_error μ ν hq0 hq1 u.continuous.measurable hf hu hb heμ heν
  have hCδ : C*δ ≤ ε := by
    have heq : (C+1)*δ = ε := by dsimp [δ]; field_simp
    nlinarith [hδ]
  exact (h u).trans (herr.trans (by dsimp only [C] at hCδ; linarith))

end RegularPointCoordinates

end

end OAI
