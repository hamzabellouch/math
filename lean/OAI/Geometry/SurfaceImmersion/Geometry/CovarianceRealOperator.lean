import OAI.Geometry.SurfaceImmersion.Geometry.LocalCovarianceParameter

namespace OAI

/-! The actual covariance correction acting on real-parameter forcing.
This form exposes linearity and does not require separate periodicity proofs
for the individual coefficients of a jet polynomial. -/
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.CovarianceCorrector

variable {E P : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def realMoment (V : C(Period, E)) (r : ℝ → ℝ) : E :=
  ∫ t in 0..1, r t • V (t : Period)

def realMeanSolution (V : C(Period, E)) (q : ℝ) (r : ℝ → ℝ) : E :=
  (meanCLM V q).inverse (realMoment V r)

def realCorrector (V : C(Period, E)) (q : ℝ) (r : ℝ → ℝ) (t : ℝ) : E :=
  let m := realMeanSolution V q r
  q⁻¹ • ((r t + inner ℝ (V (t : Period) - average V) m / q) • V (t : Period) - m)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma realMeanSolution_add (V : C(Period, E)) (q : ℝ) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    realMeanSolution V q (fun t => f t + g t) =
      realMeanSolution V q f + realMeanSolution V q g := by
  unfold realMeanSolution realMoment
  simp only [add_smul]
  have hfi : IntervalIntegrable (fun t : ℝ => f t • V (t : Period)) volume 0 1 :=
    (hf.smul (V.continuous.comp (AddCircle.continuous_mk' 1))).intervalIntegrable 0 1
  have hgi : IntervalIntegrable (fun t : ℝ => g t • V (t : Period)) volume 0 1 :=
    (hg.smul (V.continuous.comp (AddCircle.continuous_mk' 1))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hfi hgi, map_add]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma realMeanSolution_smul (V : C(Period, E)) (q a : ℝ) (f : ℝ → ℝ) :
    realMeanSolution V q (fun t => a * f t) = a • realMeanSolution V q f := by
  unfold realMeanSolution realMoment
  simp only [mul_smul, intervalIntegral.integral_smul, map_smul]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma realCorrector_add (V : C(Period, E)) (q : ℝ) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    realCorrector V q (fun s => f s + g s) t = realCorrector V q f t + realCorrector V q g t := by
  simp only [realCorrector, realMeanSolution_add V q hf hg, inner_add_right, add_div]
  module

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma realCorrector_smul (V : C(Period, E)) (q a : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    realCorrector V q (fun s => a * f s) t = a • realCorrector V q f t := by
  simp only [realCorrector, realMeanSolution_smul, inner_smul_right]
  have ha : a * f t + a * inner ℝ (V (t : Period) - average V) (realMeanSolution V q f) / q =
      a * (f t + inner ℝ (V (t : Period) - average V) (realMeanSolution V q f) / q) := by ring
  rw [ha]
  module

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup P]
  [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- Agreement with the covariance correction already used in the periodic solver. -/
lemma realCorrector_eq_parameterCorrector (V : P → C(Period, E)) (q : P → ℝ)
    (r : P → C(Period, ℝ)) (p : P) (t : ℝ) :
    realCorrector (V p) (q p) (fun s => r p (s : Period)) t =
      parameterCorrector V r q p (t : Period) := by
  have hm : realMoment (V p) (fun s => r p (s : Period)) = weightedAverage (V p) (r p) := by
    exact PeriodicPrimitive.integral_lift_eq_haar (fun s => r p s • V p s)
  simp only [realCorrector, realMeanSolution, hm, parameterCorrector,
    correctedVector, correctedScalar, covarianceSolution]

lemma contDiffOn_realMeanSolution {O : Set P} (hO : IsOpen O)
    {V : P → C(Period, E)} {q : P → ℝ} {c : P × ℝ → ℝ}
    (hV : ContDiffOn ℝ ∞ (fun z : P × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hq : ContDiffOn ℝ ∞ q O) (hqpos : ∀ p ∈ O, 0 < q p)
    (hcircle : ∀ p ∈ O, ∀ t, inner ℝ (V p t) (V p t) = q p)
    (hc : ContDiffOn ℝ ∞ c (O ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (fun p => realMeanSolution (V p) (q p) (fun t => c (p, t))) O := by
  have hM : ContDiffOn ℝ ∞ (fun p => meanCLM (V p) (q p)) O :=
    contDiffOn_const.sub ((hq.inv (fun p hp => (hqpos p hp).ne')).smul
      (contDiffOn_covarianceCLM_joint hO hV))
  have hi : ContDiffOn ℝ ∞ (fun p => (meanCLM (V p) (q p)).inverse) O := by
    apply hO.contDiffOn_iff.mpr
    intro p hp
    exact (meanCLM_isInvertible (hqpos p hp) (hcircle p hp)).contDiffAt_map_inverse.comp p
      (hM.contDiffAt (hO.mem_nhds hp))
  exact hi.clm_apply (SmoothParameterIntegral.contDiffOn_integral hO (hc.smul hV) 0 1)

lemma contDiffOn_realCorrector {O : Set P} (hO : IsOpen O)
    {V : P → C(Period, E)} {q : P → ℝ} {c : P × ℝ → ℝ}
    (hV : ContDiffOn ℝ ∞ (fun z : P × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hq : ContDiffOn ℝ ∞ q O) (hqpos : ∀ p ∈ O, 0 < q p)
    (hcircle : ∀ p ∈ O, ∀ t, inner ℝ (V p t) (V p t) = q p)
    (hc : ContDiffOn ℝ ∞ c (O ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => realCorrector (V z.1) (q z.1)
      (fun t => c (z.1, t)) z.2) (O ×ˢ Set.univ) := by
  have hm : ContDiffOn ℝ ∞ (fun z : P × ℝ =>
      realMeanSolution (V z.1) (q z.1) (fun t => c (z.1, t))) (O ×ˢ Set.univ) :=
    (contDiffOn_realMeanSolution hO hV hq hqpos hcircle hc).comp
    contDiffOn_fst (fun _ hz => hz.1)
  have hv : ContDiffOn ℝ ∞ (fun z : P × ℝ => average (V z.1)) (O ×ˢ Set.univ) :=
    (contDiffOn_average_joint hO hV).comp contDiffOn_fst (fun _ hz => hz.1)
  have hq' : ContDiffOn ℝ ∞ (fun z : P × ℝ => q z.1) (O ×ˢ Set.univ) :=
    hq.comp contDiffOn_fst (fun _ hz => hz.1)
  have hi := hq'.inv (fun z hz => (hqpos z.1 hz.1).ne')
  exact hi.smul (((hc.add (((hV.sub hv).inner ℝ hm).div hq'
    (fun z hz => (hqpos z.1 hz.1).ne'))).smul hV).sub hm)

end ClosedSurfaceR4.CovarianceCorrector

end

end OAI
