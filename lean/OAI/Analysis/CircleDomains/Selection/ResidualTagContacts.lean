import OAI.Analysis.CircleDomains.Selection.ResidualTagAvoidance

namespace OAI

/-! Application to the actual earlier residual constraints: independent
later tags can meet an earlier residual image only at the prescribed flags. -/

open Set Filter Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem ae_residual_tag_contact_in_flags
    (d e : PathCodeData X Y) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i)) (hle : e.levels = d.levels)
    (P : ProbabilityMeasure (BasePathCode d)) (Q : ProbabilityMeasure (BasePathCode e))
    (ω : TupleType → ℝ≥0∞) (hτ : meanCodeTuple e Q ≪ tupleReference ω)
    (hm : ∀ i, (support (d.levelWeights i)).Countable)
    (hweight : ∀ i, countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞)
    (hvisits : ∀ i, countingSquareNorm (fun x : support (d.levelWeights i) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hcover : ∀ i x, x ∈ support (d.levelWeights i) →
      ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (S : Set X) (hFS : ∀ n, (d.flagDeletions n : Set X) ⊆ S) :
    ∀ᵐ p ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
      ∀ s ∈ residualTimes d.dust p.1.val, ∀ k t,
        tagLeft (p.2.val.2 k) < t → t < tagRight (p.2.val.2 k) →
        p.2.val.1 t = p.1.val.1 s → p.1.val.1 s ∈ S := by
  let N : BasePathCode d → ℕ → Set UnitAddCircle := fun Γ i =>
    ⋂ n, {t | (Γ.val, t) ∈ residualIncidence d.dust univ (d.levels i) (d.flagDeletions n)}
  have hN : ∀ i, MeasurableSet {p : BasePathCode d × UnitAddCircle | p.2 ∈ N p.1 i} := by
    intro i
    simp only [N, mem_iInter, ofPred_forall]
    apply MeasurableSet.iInter
    intro n
    exact (measurableSet_residualIncidence hB isClosed_univ (hH i)
      (d.flagDeletions n).finite_toSet).preimage
        ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  have hz : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ i, volume (N Γ i) = 0 :=
    ae_all_iff.mpr fun i => ae_code_level_envelope_null d P i (hm i)
      (hweight i) (hvisits i) (hcover i)
  filter_upwards [ae_product_no_bad_tag_level P e Q ω hτ N hN hz] with p hp
  intro s hs k t hl hr heq
  by_contra hx
  have hc := (p.2.property.1.2.1 k).2.1 t hl hr
  cases hslot : p.2.val.2 k with
  | inl u =>
    simp only [hslot, tagLeft, Sum.elim_inl] at hl
    exact (not_lt_of_ge le_top) hl
  | inr q =>
    have hactive : ∃ j, (q.2.2.1 j, p.2.val.1 t) ∈ d.levels (q.2.1 j) := by
      rw [hslot] at hc
      simpa only [tagLevelGraph, activeTagLevelGraph, mem_ofPred_eq, hle] using hc
    obtain ⟨j, hj⟩ := hactive
    apply hp k q hslot j
    apply mem_iInter.mpr
    intro n
    exact ⟨s, hs, mem_univ s, heq ▸ hj, fun h => hx (hFS n h)⟩

end CircleDomainRigidity

end

end OAI
