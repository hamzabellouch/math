import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialNonzero

namespace OAI

/-! Meromorphic continuation of the literal nonzero arithmetic Fourier
Dirichlet coefficients, obtained from the actual automorphic resolvent. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaRadialTest_eventually_ne_zero {h : Eisenstein} (hh : h≠0) (s : ℂ) :
    ∀ᶠ z in 𝓝[≠] s, cubicThetaFourierRadialTest h cubicThetaRadialTestWeight z≠0 := by
  have ha := (cubicThetaFourierRadialTest_entire hh cubicThetaRadialTestWeight).analyticAt
  rcases (ha s).eventually_eq_zero_or_eventually_ne_zero with hz | hn
  · have hg : AnalyticOnNhd ℂ (cubicThetaFourierRadialTest h cubicThetaRadialTestWeight) univ :=
      fun z _ => ha z
    have he := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ s) hz
    exact False.elim (cubicThetaFourierRadialTest_nonzero hh (he (mem_univ 2)))
  · exact hn

lemma cubicThetaGamma_analytic_right {s : ℂ} (hs : 0<s.re) : AnalyticAt ℂ Complex.Gamma s := by
  have hd : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0<z.re} := by
    intro z hz
    apply (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m hm
    have he := congrArg Complex.re hm
    simp only [Complex.neg_re,Complex.natCast_re] at he
    have hn : 0≤(m:ℝ) := Nat.cast_nonneg m
    change 0<z.re at hz
    linarith
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)

def cubicThetaFrequencyQuotient (h : Eisenstein) (s : ℂ) : ℂ :=
  Complex.Gamma s*cubicThetaCuspFourierObservable h cubicThetaRadialTestWeight s/
    ((Real.pi:ℂ)*cubicThetaFourierRadialTest h cubicThetaRadialTestWeight s)

lemma cubicThetaFrequencyQuotient_meromorphic {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 1<s.re) : MeromorphicAt (cubicThetaFrequencyQuotient h) s := by
  exact ((cubicThetaGamma_analytic_right (by linarith)).meromorphicAt.mul
    (cubicThetaCuspFourierObservable_meromorphic h cubicThetaRadialTestWeight hs)).div
      ((MeromorphicAt.const (Real.pi:ℂ) s).mul
        ((cubicThetaFourierRadialTest_entire hh cubicThetaRadialTestWeight).analyticAt s).meromorphicAt)

lemma cubicThetaFrequencyQuotient_right {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 3<s.re)
    (hR : cubicThetaFourierRadialTest h cubicThetaRadialTestWeight s≠0) :
    cubicThetaFrequencyQuotient h s=cubicThetaFrequencyDirichlet h s := by
  have hG := Complex.Gamma_ne_zero_of_re_pos (show 0<s.re by linarith)
  have hp : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  rw [cubicThetaFrequencyQuotient,cubicThetaCuspFourierObservable_normalized hh _ hs]
  field_simp

def cubicThetaFrequencyContinuation (h : Eisenstein) (s : ℂ) : ℂ :=
  if 3<s.re then cubicThetaFrequencyDirichlet h s else cubicThetaFrequencyQuotient h s

theorem cubicThetaFrequencyContinuation_right (h : Eisenstein) {s : ℂ} (hs : 3<s.re) :
    cubicThetaFrequencyContinuation h s=cubicThetaFrequencyDirichlet h s :=
  ite_eq_left hs

theorem cubicThetaFrequencyContinuation_meromorphic {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 1<s.re) : MeromorphicAt (cubicThetaFrequencyContinuation h) s := by
  by_cases hs3 : 3<s.re
  · have hd : DifferentiableOn ℂ (cubicThetaFrequencyDirichlet h) {z : ℂ | 2<z.re} :=
      fun z hz => (cubicThetaFrequencyDirichlet_differentiableAt h hz).differentiableWithinAt
    have ha := hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 2<s.re by linarith))
    apply ha.meromorphicAt.congr
    have hn : ∀ᶠ z in 𝓝 s, 3<z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs3
    filter_upwards [nhdsWithin_le_nhds hn] with z hz
    exact (cubicThetaFrequencyContinuation_right h hz).symm
  · apply (cubicThetaFrequencyQuotient_meromorphic hh hs).congr
    filter_upwards [cubicThetaRadialTest_eventually_ne_zero hh s] with z hz
    unfold cubicThetaFrequencyContinuation
    split_ifs with hz3
    · exact cubicThetaFrequencyQuotient_right hh hz3 hz
    · rfl

end CubicFirstMoment

end

end OAI
