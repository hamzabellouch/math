import OAI.Analysis.CircleDomains.Rigidity.CodeFreeTrace

namespace OAI

/-! Combining the actual residual constraints with null incidence sets
on the open tags needs no globally chosen circle trace. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem ae_code_free_level_incidence_null_of_tags
    (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d)) (i : ℕ)
    (Free : Set X) (hFree : Free ⊆ d.dust)
    (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (d.levelWeights i) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hcover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdelete : ∀ n, Disjoint Free (d.flagDeletions n : Set X))
    (htags : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ k,
      volume {θ | ∃ t ∈ Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)),
        Γ.val.1 t ∈ Free ∧ (θ, Γ.val.1 t) ∈ d.levels i} = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      volume {θ | ∃ x ∈ range Γ.val.1 ∩ Free, (θ, x) ∈ d.levels i} = 0 := by
  filter_upwards [ae_code_level_envelope_null d P i hm hweight hvisits hcover, htags]
    with Γ hres htag
  apply measure_mono_null (t :=
    (⋂ n, {θ | (Γ.val, θ) ∈ residualIncidence d.dust univ (d.levels i) (d.flagDeletions n)}) ∪
    ⋃ k, {θ | ∃ t ∈ Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)),
      Γ.val.1 t ∈ Free ∧ (θ, Γ.val.1 t) ∈ d.levels i}) _
    (measure_union_null hres (measure_iUnion_null htag))
  rintro θ ⟨x, ⟨⟨t, rfl⟩, hx⟩, hθ⟩
  by_cases ht : ∃ k, t ∈ Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k))
  · obtain ⟨k, hk⟩ := ht
    exact Or.inr (mem_iUnion.mpr ⟨k, t, hk, hx, hθ⟩)
  · apply Or.inl
    apply mem_iInter.mpr
    intro n
    refine ⟨t, ?_, mem_univ _, hθ, fun hp => disjoint_left.mp (hdelete n) hx hp⟩
    rw [residualTimes_eq]
    exact ⟨hFree hx, fun h => ht (mem_iUnion.mp h)⟩

end CircleDomainRigidity

end OAI
