import OAI.NumberTheory.Jacobsthal.Estimates.ConsecutivePowerProjection

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.KernelPotential

noncomputable def canonicalPairVisitKernel (a : ℕ) (v H : ℝ) : Kernel (RawHistory a) FiniteRawHistory :=
  Kernel.sum (fun n : ℕ => (pairStoppedHistory a n v H).map (@Sigma.mk ℕ RawHistory (a+2*n+1)))

instance canonicalPairVisitKernel_isSFiniteKernel (a : ℕ) (v H : ℝ) : IsSFiniteKernel (canonicalPairVisitKernel a v H) := by
  unfold canonicalPairVisitKernel
  infer_instance

theorem canonicalPairVisit_endpoint (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    (canonicalPairVisitKernel a v H past).map finiteRawLast=consecutiveMarkedHit v H (rawLast a past) := by
  rw [canonicalPairVisitKernel,Kernel.sum_apply,Measure.map_sum finiteRawLast_measurable.aemeasurable,
    consecutiveMarkedHit,potential,Kernel.sum_apply]
  apply congrArg Measure.sum
  funext n
  rw [Kernel.map_apply _ (measurableSigmaMk (a+2*n+1)),
    Measure.map_map finiteRawLast_measurable (measurableSigmaMk (a+2*n+1))]
  exact pairStoppedHistory_projection a n v H past

lemma canonicalPairVisit_mass (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    canonicalPairVisitKernel a v H past univ=consecutiveMarkedHit v H (rawLast a past) univ := by
  have he := congrArg (fun μ : Measure CostState => μ univ) (canonicalPairVisit_endpoint a v H past)
  rw [Measure.map_apply finiteRawLast_measurable MeasurableSet.univ,preimage_univ] at he
  exact he

lemma canonicalPairVisit_mass_le_one (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    canonicalPairVisitKernel a v H past univ ≤ 1 := by
  rw [canonicalPairVisit_mass]
  exact consecutiveMarkedHit_mass_le_one v H _

instance canonicalPairVisitKernel_isFiniteKernel (a : ℕ) (v H : ℝ) : IsFiniteKernel (canonicalPairVisitKernel a v H) :=
  ⟨⟨1,by simp,canonicalPairVisit_mass_le_one a v H⟩⟩

noncomputable def extendFinitePrefix (N : ℕ) : Kernel FiniteRawHistory (RawHistory N) where
  toFun q := if q.1 ≤ N then rawExtension q.1 N q.2 else 0
  measurable' := by
    apply measurable_sigma_family
    intro n
    by_cases hn : n ≤ N
    · simpa only [hn,ite_true] using (rawExtension n N).measurable
    · simp only [hn,ite_false]
      exact measurable_const

instance extendFinitePrefix_isFiniteKernel (N : ℕ) : IsFiniteKernel (extendFinitePrefix N) := by
  refine ⟨⟨1,by simp,?_⟩⟩
  intro q
  change (if q.1 ≤ N then rawExtension q.1 N q.2 else 0) univ ≤ 1
  split_ifs <;> simp

lemma extendFinitePrefix_comp_map {α : Type*} [MeasurableSpace α] (N n : ℕ)
    (K : Kernel α (RawHistory n)) [IsSFiniteKernel K] :
    extendFinitePrefix N ∘ₖ K.map (@Sigma.mk ℕ RawHistory n)=
      if n ≤ N then rawExtension n N ∘ₖ K else 0 := by
  ext x S hS
  rw [Kernel.comp_apply' _ _ _ hS,Kernel.map_apply _ (measurableSigmaMk n),
    lintegral_map ((extendFinitePrefix N).measurable_coe hS) (measurableSigmaMk n)]
  by_cases hn : n ≤ N
  · rw [ite_eq_left hn,Kernel.comp_apply' _ _ _ hS]
    apply lintegral_congr
    intro h
    change (if n ≤ N then rawExtension n N h else 0) S=rawExtension n N h S
    rw [ite_eq_left hn]
  · rw [ite_eq_right hn]
    change (∫⁻ h, (if n ≤ N then rawExtension n N h else 0) S ∂K x)=0
    simp [hn]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
