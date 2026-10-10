import OAI.Probability.InvariantIsing.Haar.HaarExponentialLimit
import OAI.Probability.InvariantIsing.Haar.HerbstDifferential

namespace OAI

/-! Exponential moments and their derivatives for polynomial observables on SO(N). -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

def haarPolynomialMoment {N : ℕ} (μ : Measure (SpecialOrthogonal N)) (p : MatrixPolynomial N) (t : ℝ) : ℝ :=
  ∫ U, Real.exp (t*haarPolynomialValue p U) ∂μ

def haarPolynomialMomentDerivative {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    (p : MatrixPolynomial N) (t : ℝ) : ℝ :=
  ∫ U, haarPolynomialValue p U*Real.exp (t*haarPolynomialValue p U) ∂μ

lemma haarPolynomialMoment_pos {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] (p : MatrixPolynomial N) (t : ℝ) :
    0 < haarPolynomialMoment μ p t :=
  integral_exp_pos (continuous_haar_integrable μ _
    (Real.continuous_exp.comp (continuous_const.mul (continuous_haarPolynomialValue p))))

@[simp] lemma haarPolynomialMoment_zero {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] (p : MatrixPolynomial N) : haarPolynomialMoment μ p 0 = 1 := by
  simp [haarPolynomialMoment]

@[simp] lemma haarPolynomialMomentDerivative_zero {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    (p : MatrixPolynomial N) :
    haarPolynomialMomentDerivative μ p 0 = ∫ U, haarPolynomialValue p U ∂μ := by
  simp only [haarPolynomialMomentDerivative,zero_mul,Real.exp_zero,mul_one]

lemma haarPolynomialMoment_hasDerivAt {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] (p : MatrixPolynomial N) (t : ℝ) :
    HasDerivAt (haarPolynomialMoment μ p) (haarPolynomialMomentDerivative μ p t) t := by
  let F' (s : ℝ) (U : SpecialOrthogonal N) :=
    haarPolynomialValue p U*Real.exp (s*haarPolynomialValue p U)
  have hc : Continuous (fun z : ℝ × SpecialOrthogonal N => F' z.1 z.2) := by
    have hp := (continuous_haarPolynomialValue p).comp (continuous_snd : Continuous fun z : ℝ × SpecialOrthogonal N => z.2)
    exact hp.mul (Real.continuous_exp.comp (continuous_fst.mul hp))
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (Set.univ : Set (SpecialOrthogonal N)))).exists_bound_of_continuousOn
    (show ContinuousOn (fun z => F' z.1 z.2) (Icc (t-1) (t+1) ×ˢ Set.univ) from hc.continuousOn)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (s := Ioo (t-1) (t+1)) (F' := F') (bound := fun _ => B)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s => (Real.continuous_exp.comp
      (continuous_const.mul (continuous_haarPolynomialValue p))).measurable.aestronglyMeasurable)
    (continuous_haar_integrable μ _ (Real.continuous_exp.comp
      (continuous_const.mul (continuous_haarPolynomialValue p))))
    ((hc.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable)
    (ae_of_all μ fun U s hs => hB (s,U) ⟨⟨hs.1.le,hs.2.le⟩,mem_univ _⟩)
    (integrable_const B) ?_).2
  apply ae_of_all
  intro U s _
  convert ((hasDerivAt_id s).mul_const (haarPolynomialValue p U)).exp using 1
  all_goals simp only [F',id_eq,Function.comp_apply,Pi.mul_apply]
  all_goals ring

end InvariantIsing

end

end OAI
