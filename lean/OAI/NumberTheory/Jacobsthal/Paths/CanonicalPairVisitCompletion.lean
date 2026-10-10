import OAI.NumberTheory.Jacobsthal.Probability.CanonicalPairVisitLaw

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical

theorem canonicalPairVisit_completion (a N : ℕ) (v H : ℝ) :
    extendFinitePrefix N ∘ₖ canonicalPairVisitKernel a v H=
      (rawExtension a N).restrict (anyPairHit_measurable a N v H) := by
  rw [canonicalPairVisitKernel,Kernel.comp_sum_right,← completedPairHit_sum]
  apply congrArg Kernel.sum
  funext n
  rw [extendFinitePrefix_comp_map]
  by_cases hn : a+2*n+1 ≤ N
  · rw [ite_eq_left hn,completedPairHit_eq_extension hn]
  · rw [ite_eq_right hn]
    ext past S hS
    rw [completedPairHit,Kernel.restrict_apply' _ _ _ hS,boundedPairCylinder,
      dite_eq_right hn,inter_empty]
    simp

theorem canonicalPairVisit_completion_le (a N : ℕ) (v H : ℝ) (past : RawHistory a) :
    (extendFinitePrefix N ∘ₖ canonicalPairVisitKernel a v H) past ≤ rawExtension a N past := by
  rw [canonicalPairVisit_completion,Kernel.restrict_apply]
  exact Measure.restrict_le_self

theorem canonicalPairVisit_bounded_mass (a N : ℕ) (v H : ℝ) (past : RawHistory a) :
    canonicalPairVisitKernel a v H past {q | q.1 ≤ N}=rawExtension a N past (anyPairHit a N v H) := by
  have he := congrArg (fun K : Kernel (RawHistory a) (RawHistory N) => K past univ)
    (canonicalPairVisit_completion a N v H)
  rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ,Kernel.restrict_apply' _ _ _ MeasurableSet.univ,univ_inter] at he
  have hi : (fun q : FiniteRawHistory => extendFinitePrefix N q univ)=
      {q : FiniteRawHistory | q.1 ≤ N}.indicator (fun _ => (1:ℝ≥0∞)) := by
    funext q
    by_cases hq : q.1 ≤ N <;> simp [extendFinitePrefix,hq]
  rw [hi,lintegral_indicator (measurableSet_le finiteRawLength_measurable measurable_const)] at he
  simpa only [lintegral_const,one_mul,Measure.restrict_apply MeasurableSet.univ,univ_inter] using he

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
