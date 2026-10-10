import OAI.Analysis.CircleDomains.Sobolev.LocalBoundedSobolevChain
import OAI.Analysis.CircleDomains.Sobolev.CompactWeakExtension
import OAI.Analysis.CircleDomains.Rigidity.SmoothTraceTruncation
import OAI.Analysis.CircleDomains.Sobolev.SobolevRepresentative

namespace OAI

/-! Truncating a continuous zero trace produces genuine global weak
partial derivatives, supported away from the excluded closed set. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_trace_truncation_weak
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u) (hb : ∀ x, u x ∈ Icc 0 1)
    (hz : ∀ x ∉ U, u x = 0) (hw : DeGiorgi.MemW1pWitness 2 u U)
    {δ : ℝ} (hδ : 0 < δ) (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => deriv (smoothTraceTruncation δ) (u x) * U.indicator (fun x => hw.weakGrad x i) x)
      (smoothTraceTruncation δ ∘ u) univ := by
  let K : Set EuclideanPlane := {x | δ ≤ u x}
  have hK : IsCompact K := hs.isCompact.of_isClosed_subset
    (isClosed_le continuous_const hu) (by
      intro x hx
      apply subset_tsupport u
      change u x ≠ 0
      linarith [show δ ≤ u x from hx])
  have hKU : K ⊆ U := by
    intro x hx
    by_contra hxU
    have he := hz x hxU
    have ht : δ ≤ u x := hx
    linarith
  apply weakPartial_global_of_compact_support hU hK hKU
  · apply (bounded_sobolev_chain_rule_on hU hw (fun x _ => hb x)
      ((smoothTraceTruncation_contDiff δ).of_le (by simp)) i).congr_ae Filter.EventuallyEq.rfl
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [indicator_of_mem hx]
  · intro x hx
    exact smoothTraceTruncation_zero hδ (le_of_not_ge hx)
  · intro x hx
    rw [smoothTraceTruncation_deriv_zero hδ (le_of_not_ge hx), zero_mul]

end CircleDomainRigidity

end

end OAI
