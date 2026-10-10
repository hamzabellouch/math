import OAI.Analysis.CircleDomains.Selection.CodeResidualAvoidance

namespace OAI

/-! Borel envelopes allow Tonelli to remove diffuse residual contacts
without assuming that an uncountable incidence projection is Borel. -/

open Set Filter Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [TopologicalSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z] [BorelSpace Z]

theorem ae_no_residual_incidence_of_null_envelopes
    (d : PathCodeData X Y) (hB : IsClosed d.dust)
    (R : Set (Z × X)) (hR : IsClosed R)
    (P : ProbabilityMeasure (BasePathCode d)) (ν : Measure Z) [SFinite ν]
    (F : ℕ → Finset X) (S : Set X) (hFS : ∀ n, (F n : Set X) ⊆ S)
    (hnull : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      ν (⋂ n, {z | (Γ.val, z) ∈ residualIncidence d.dust univ R (F n)}) = 0) :
    ∀ᵐ q ∂((P : Measure (BasePathCode d)).prod ν),
      ∀ t ∈ residualTimes d.dust q.1.val, (q.2, q.1.val.1 t) ∈ R → q.1.val.1 t ∈ S := by
  let E : Set (BasePathCode d × Z) :=
    ⋂ n, {q | (q.1.val, q.2) ∈ residualIncidence d.dust univ R (F n)}
  have hE : MeasurableSet E := by
    apply MeasurableSet.iInter
    intro n
    exact (measurableSet_residualIncidence hB isClosed_univ hR (F n).finite_toSet).preimage
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  have hzero : ((P : Measure (BasePathCode d)).prod ν) E = 0 := by
    rw [Measure.prod_apply hE]
    calc
      _ = ∫⁻ _Γ, (0 : ℝ≥0∞) ∂(P : Measure (BasePathCode d)) := by
        apply lintegral_congr_ae
        filter_upwards [hnull] with Γ hΓ
        simpa only [E, preimage_iInter, preimage_ofPred_eq, Prod.mk.injEq] using hΓ
      _ = 0 := by simp
  have hae : ∀ᵐ q ∂((P : Measure (BasePathCode d)).prod ν), q ∉ E := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using hzero
  filter_upwards [hae] with q hq
  intro t ht hR
  by_contra hS
  apply hq
  apply mem_iInter.mpr
  intro n
  exact ⟨t, ht, mem_univ t, hR, fun h => hS (hFS n h)⟩

end CircleDomainRigidity

end

end OAI
