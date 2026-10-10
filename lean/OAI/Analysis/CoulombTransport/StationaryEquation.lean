import OAI.Analysis.CoulombTransport.GeometryJets

namespace OAI

universe uE

noncomputable section

namespace Problem356.GeometryJets

open CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The state gradient of the regularized three-body Coulomb cost.
The input is `(parameter, (central point, negative outer point))`. -/
def stationaryEquation (K : ℝ) (a : E) (p : E × (E × E)) : E × E :=
  (pairGradient (p.2.1 - p.1) + pairGradient (p.2.1 - p.2.2) + K • p.2.1,
   -pairGradient (p.2.1 - p.2.2) - pairGradient (p.1 - p.2.2) -
     (5 / 4 : ℝ) • a + K • (p.2.2 + a))

/-- The center state Hessian, expressed using the single-pair unit-center Hessian. -/
def centerStateHessian (K : ℝ) (Q : E →L[ℝ] E) : (E × E) →L[ℝ] (E × E) :=
  (((2 : ℝ) • Q + K • ContinuousLinearMap.id ℝ E).comp
      (ContinuousLinearMap.fst ℝ E E) - Q.comp (ContinuousLinearMap.snd ℝ E E)).prod
    (-(Q.comp (ContinuousLinearMap.fst ℝ E E)) +
      ((9 / 8 : ℝ) • Q + K • ContinuousLinearMap.id ℝ E).comp
        (ContinuousLinearMap.snd ℝ E E))

/-- The center derivative with respect to the moving positive outer point. -/
def centerParameterDerivative (Q : E →L[ℝ] E) : E →L[ℝ] (E × E) :=
  (-Q).prod ((-1 / 8 : ℝ) • Q)

lemma stationaryEquation_center (K : ℝ) (a : E) (ha : ‖a‖ = 1) :
    stationaryEquation K a (a, (0, -a)) = 0 := by
  have hvec : a - -a = (2 : ℝ) • a := by module
  simp [stationaryEquation, pairGradient, hvec, norm_smul, ha]
  module

private lemma hessian_neg_center (a : E) : pairHessian (-a) = pairHessian a := by
  apply ContinuousLinearMap.ext
  intro v
  simp [pairHessian, innerSL, ContinuousLinearMap.smulRight_apply]

private lemma hessian_double_center (a : E) (ha : ‖a‖ = 1) :
    pairHessian ((2 : ℝ) • a) = (1 / 8 : ℝ) • pairHessian a := by
  apply ContinuousLinearMap.ext
  intro v
  simp [pairHessian, innerSL, ContinuousLinearMap.smulRight_apply, norm_smul, ha]
  module

lemma hasFDerivAt_stationary_state_center (K : ℝ) (a : E) (ha : ‖a‖ = 1) :
    HasFDerivAt (fun p : E × E => stationaryEquation K a (a, p))
      (centerStateHessian K (pairHessian a)) (0, -a) := by
  have ha0 := center_nonzero ha
  have hneg : -a ≠ 0 := neg_ne_zero.mpr ha0
  have hvec : a - -a = (2 : ℝ) • a := by module
  have hdouble : a - -a ≠ 0 := by
    rw [hvec]
    exact smul_ne_zero (by norm_num) ha0
  have hf : HasFDerivAt (fun p : E × E => p.1)
      (ContinuousLinearMap.fst ℝ E E) (0, -a) := hasFDerivAt_fst
  have hz : HasFDerivAt (fun p : E × E => p.2)
      (ContinuousLinearMap.snd ℝ E E) (0, -a) := hasFDerivAt_snd
  have h1 := (hasFDerivAt_pairGradient (show (0 : E) - a ≠ 0 by simpa using hneg)).comp
    (0, -a) (hf.sub_const a)
  have h2 := (hasFDerivAt_pairGradient (show (0 : E) - -a ≠ 0 by simpa using ha0)).comp
    (0, -a) (hf.sub hz)
  have h3 := (hasFDerivAt_pairGradient hdouble).comp (0, -a) (hz.const_sub a)
  have hx := (h1.add h2).add (hf.const_smul K)
  have hzz := ((h2.neg.sub h3).sub_const ((5 / 4 : ℝ) • a)).add
    ((hz.add_const a).const_smul K)
  convert! hx.prodMk hzz using 1
  apply ContinuousLinearMap.ext
  intro p
  simp [centerStateHessian, hvec, hessian_double_center a ha]
  constructor <;> module

lemma hasFDerivAt_stationary_parameter_center (K : ℝ) (a : E) (ha : ‖a‖ = 1) :
    HasFDerivAt (fun y : E => stationaryEquation K a (y, (0, -a)))
      (centerParameterDerivative (pairHessian a)) a := by
  have ha0 := center_nonzero ha
  have hneg : -a ≠ 0 := neg_ne_zero.mpr ha0
  have hvec : a - -a = (2 : ℝ) • a := by module
  have hdouble : a - -a ≠ 0 := by
    rw [hvec]
    exact smul_ne_zero (by norm_num) ha0
  have hy := hasFDerivAt_id (𝕜 := ℝ) a
  have h1 := (hasFDerivAt_pairGradient (show (0 : E) - a ≠ 0 by simpa using hneg)).comp
    a (hy.const_sub 0)
  have h3 := (hasFDerivAt_pairGradient hdouble).comp a (hy.sub_const (-a))
  have hx := (h1.add_const (pairGradient ((0 : E) - -a))).add_const (K • (0 : E))
  have hz := ((h3.const_sub (-pairGradient ((0 : E) - -a))).sub_const
    ((5 / 4 : ℝ) • a)).add_const (K • (-a + a))
  convert! hx.prodMk hz using 1
  apply ContinuousLinearMap.ext
  intro p
  simp [centerParameterDerivative, hvec, hessian_double_center a ha]
  module

lemma contDiffAt_stationaryEquation {n : WithTop ENat} (K : ℝ) (a : E)
    (p : E × (E × E)) (hxy : p.2.1 ≠ p.1) (hxz : p.2.1 ≠ p.2.2)
    (hyz : p.1 ≠ p.2.2) : ContDiffAt ℝ n (stationaryEquation K a) p := by
  have hy : ContDiffAt ℝ n (fun q : E × (E × E) => q.1) p := contDiffAt_fst
  have hx : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.1) p := contDiffAt_snd.fst
  have hz : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.2) p := contDiffAt_snd.snd
  have h1 := (contDiffAt_pairGradient (n := n) (sub_ne_zero.mpr hxy)).comp p (hx.sub hy)
  have h2 := (contDiffAt_pairGradient (n := n) (sub_ne_zero.mpr hxz)).comp p (hx.sub hz)
  have h3 := (contDiffAt_pairGradient (n := n) (sub_ne_zero.mpr hyz)).comp p (hy.sub hz)
  exact ((h1.add h2).add (hx.const_smul K)).prodMk
    (((h2.neg.sub h3).sub contDiffAt_const).add ((hz.add contDiffAt_const).const_smul K))

lemma contDiffAt_stationaryEquation_center {n : WithTop ENat}
    (K : ℝ) (a : E) (ha : ‖a‖ = 1) :
    ContDiffAt ℝ n (stationaryEquation K a) (a, (0, -a)) := by
  have ha0 := center_nonzero ha
  apply contDiffAt_stationaryEquation
  · exact ha0.symm
  · exact (neg_ne_zero.mpr ha0).symm
  · intro h
    have hnorm : ‖a - -a‖ = 2 := by
      have hvec : a - -a = (2 : ℝ) • a := by module
      rw [hvec, norm_smul, ha]
      norm_num
    change a = -a at h
    rw [sub_eq_zero.mpr h, norm_zero] at hnorm
    norm_num at hnorm

/-- Total differential with the parameter block followed by the state block. -/
def centerTotalDerivative (K : ℝ) (Q : E →L[ℝ] E) :
    (E × (E × E)) →L[ℝ] (E × E) :=
  (centerParameterDerivative Q).comp (ContinuousLinearMap.fst ℝ E (E × E)) +
    (centerStateHessian K Q).comp (ContinuousLinearMap.snd ℝ E (E × E))

lemma hasFDerivAt_stationary_center (K : ℝ) (a : E) (ha : ‖a‖ = 1) :
    HasFDerivAt (stationaryEquation K a)
      (centerTotalDerivative K (pairHessian a)) (a, (0, -a)) := by
  have ha0 := center_nonzero ha
  have hneg : -a ≠ 0 := neg_ne_zero.mpr ha0
  have hvec : a - -a = (2 : ℝ) • a := by module
  have hdouble : a - -a ≠ 0 := by
    rw [hvec]
    exact smul_ne_zero (by norm_num) ha0
  have hy : HasFDerivAt (fun p : E × (E × E) => p.1)
      (ContinuousLinearMap.fst ℝ E (E × E)) (a, (0, -a)) := hasFDerivAt_fst
  have hs : HasFDerivAt (fun p : E × (E × E) => p.2)
      (ContinuousLinearMap.snd ℝ E (E × E)) (a, (0, -a)) := hasFDerivAt_snd
  have hx := hs.fst
  have hz := hs.snd
  have h1 := (hasFDerivAt_pairGradient (show (0 : E) - a ≠ 0 by simpa using hneg)).comp
    (a, (0, -a)) (hx.sub hy)
  have h2 := (hasFDerivAt_pairGradient (show (0 : E) - -a ≠ 0 by simpa using ha0)).comp
    (a, (0, -a)) (hx.sub hz)
  have h3 := (hasFDerivAt_pairGradient hdouble).comp (a, (0, -a)) (hy.sub hz)
  have hfirst := (h1.add h2).add (hx.const_smul K)
  have hsecond := ((h2.neg.sub h3).sub_const ((5 / 4 : ℝ) • a)).add
    ((hz.add_const a).const_smul K)
  convert! hfirst.prodMk hsecond using 1
  apply ContinuousLinearMap.ext
  intro p
  simp [centerTotalDerivative, centerParameterDerivative, centerStateHessian,
    hvec, hessian_double_center a ha]
  constructor <;> module

end Problem356.GeometryJets

end

end OAI
