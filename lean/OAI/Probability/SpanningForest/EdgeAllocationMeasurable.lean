import OAI.Probability.SpanningForest.EdgeAllocation

namespace OAI

noncomputable section
namespace Problem336.EdgeAllocation

@[fun_prop]
theorem measurable_neighborRank (u v : ℕ) :
    Measurable (fun q : GraphCode × (ℕ → ℝ) => neighborRank q.1 q.2 u v) := by
  apply measurable_ncard.comp
  apply measurable_set_iff.mpr
  intro w
  change Measurable (fun q : GraphCode × (ℕ → ℝ) =>
    q.1.1 u w = true ∧ q.2 w < q.2 v)
  apply Measurable.and
  · have h : Measurable (fun q : GraphCode × (ℕ → ℝ) => q.1.1 u w) :=
      (measurable_pi_apply w).comp ((measurable_pi_apply u).comp
        (measurable_subtype_coe.comp measurable_fst))
    exact h.eq_const true
  · exact measurableSet_setOfPred.mp
      (measurableSet_lt (measurable_snd.eval) (measurable_snd.eval))

@[fun_prop]
theorem measurable_neighborRank_joint :
    Measurable (fun q : (GraphCode × (ℕ → ℝ)) × (ℕ × ℕ) =>
      neighborRank q.1.1 q.1.2 q.2.1 q.2.2) :=
  measurable_from_prod_countable_left fun p => measurable_neighborRank p.1 p.2

@[fun_prop]
theorem measurable_source (e : EdgeCode) :
    Measurable (fun key : ℕ → ℝ => source key e) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)

@[fun_prop]
theorem measurable_target (e : EdgeCode) :
    Measurable (fun key : ℕ → ℝ => target key e) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)

@[fun_prop]
theorem measurable_source_joint :
    Measurable (fun q : (ℕ → ℝ) × EdgeCode => source q.1 q.2) :=
  measurable_from_prod_countable_left measurable_source

@[fun_prop]
theorem measurable_target_joint :
    Measurable (fun q : (ℕ → ℝ) × EdgeCode => target q.1 q.2) :=
  measurable_from_prod_countable_left measurable_target

@[fun_prop]
theorem measurable_coordinate :
    Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      coordinate q.1.1 q.1.2 q.2) := by
  have hs : Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      source q.1.2 q.2) :=
    measurable_source_joint.comp (measurable_fst.snd.prodMk measurable_snd)
  have ht : Measurable (fun q : (GraphCode × (ℕ → ℝ)) × EdgeCode =>
      target q.1.2 q.2) :=
    measurable_target_joint.comp (measurable_fst.snd.prodMk measurable_snd)
  exact hs.prodMk (measurable_neighborRank_joint.comp
    (measurable_fst.prodMk (hs.prodMk ht)))

end Problem336.EdgeAllocation

end

end OAI
