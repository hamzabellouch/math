import OAI.Probability.SLE.Mass.RadonTestLimit
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

/-! A countable list of positive Radon measures approximates every finite
list of compact-test integrals. This uses separability of the image in
real sequence space, without a topology on the space of measures. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped Topology CompactlySupported

namespace SLEExactGauge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [T2Space X] [LocallyCompactSpace X] [BorelSpace X] in
lemma LocalTestFamily.exists_countable_measure_approximants (D : LocalTestFamily X) :
    ∃ μ : ℕ → Measure X, (∀ k, (μ k).Regular) ∧
      ∀ (ν : Measure X), ν.Regular → ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
        ∃ k, ∀ j < n+1, |(∫ x, D.test j x ∂μ k)-(∫ x, D.test j x ∂ν)| < ε := by
  let R := {ν : Measure X // ν.Regular}
  let V : R → ℕ → ℝ := fun ν j => ∫ x, D.test j x ∂ν.val
  let S := range V
  let : Nonempty S := ⟨⟨V ⟨0,inferInstance⟩,⟨⟨0,inferInstance⟩,rfl⟩⟩⟩
  let q : ℕ → S := TopologicalSpace.denseSeq S
  have hq : DenseRange q := TopologicalSpace.denseRange_denseSeq S
  choose μ hμ using fun k => (q k).property
  refine ⟨fun k => (μ k).val,fun k => (μ k).property,?_⟩
  intro ν hν n ε hε
  let v : S := ⟨V ⟨ν,hν⟩,⟨⟨ν,hν⟩,rfl⟩⟩
  let U : Set S := {w | ∀ j : Fin (n+1), |w.val j.val-v.val j.val| < ε}
  have hU : IsOpen U := by
    simp only [U,Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt (((continuous_apply j.val).comp continuous_subtype_val).sub continuous_const).abs
      continuous_const
  have hv : v ∈ U := by
    intro j
    simpa only [sub_self,abs_zero] using hε
  obtain ⟨k,hk⟩ := hq.exists_mem_open hU ⟨v,hv⟩
  refine ⟨k,fun j hj => ?_⟩
  have hh := hk (⟨j,hj⟩ : Fin (n+1))
  change |(V (μ k)) j-(V ⟨ν,hν⟩) j| < ε
  rw [hμ k]
  exact hh

end SLEExactGauge

end

end OAI
