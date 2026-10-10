import OAI.Analysis.CircleDomains.Sobolev.LocalBoundedSobolevChain
import OAI.Analysis.CircleDomains.Sobolev.CompactWeakExtension
import OAI.Analysis.CircleDomains.Rigidity.SignedTraceTruncation
import OAI.Analysis.CircleDomains.Sobolev.SobolevRepresentative

namespace OAI

/-! Signed zero-trace truncations have global weak derivatives, with no
regularity assumption on the excluded set. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem signed_trace_truncation_weak
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (hz : ∀ x ∉ U, u x = 0) (hw : DeGiorgi.MemW1pWitness 2 u U)
    {δ : ℝ} (hδ : 0 < δ) (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => deriv (signedTraceTruncation δ) (u x) * U.indicator (fun x => hw.weakGrad x i) x)
      (signedTraceTruncation δ ∘ u) univ := by
  obtain ⟨B, hbound⟩ := hu.bounded_above_of_compact_support hs
  have hB : 0 ≤ B := (norm_nonneg (u 0)).trans (hbound 0)
  have hb : ∀ x ∈ U, u x ∈ Icc (-B) B := by
    intro x _
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hbound x)
  let K : Set EuclideanPlane := {x | δ ≤ |u x|}
  have hK : IsCompact K := hs.isCompact.of_isClosed_subset
    (isClosed_le continuous_const hu.abs) (by
      intro x hx
      apply subset_tsupport u
      change u x ≠ 0
      intro he
      have ht : δ ≤ |u x| := hx
      rw [he, abs_zero] at ht
      exact (not_le_of_gt hδ) ht)
  have hKU : K ⊆ U := by
    intro x hx
    by_contra hxU
    have ht : δ ≤ |u x| := hx
    rw [hz x hxU, abs_zero] at ht
    exact (not_le_of_gt hδ) ht
  apply weakPartial_global_of_compact_support hU hK hKU
  · apply (bounded_sobolev_chain_rule_on_symmetric hU hw hB hb
      ((signedTraceTruncation_contDiff δ).of_le (by simp)) i).congr_ae Filter.EventuallyEq.rfl
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [indicator_of_mem hx]
  · intro x hx
    exact signedTraceTruncation_zero hδ (le_of_not_ge hx)
  · intro x hx
    rw [signedTraceTruncation_deriv_zero hδ (le_of_not_ge hx), zero_mul]

end CircleDomainRigidity

end

end OAI
