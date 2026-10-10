import OAI.NumberTheory.DukePrimeDegree.Entropy.SmallHeightEntropy
import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientLogProper

namespace OAI

/-! # Compact exhaustion with arbitrarily small height entropy -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_compact_height_small_entropy {n : ℕ}
    (μ : Measure (X n)) [IsProbabilityMeasure μ] (a : G n)
    (ha : MeasurePreserving (fun x => rightAction x a) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : X n → ℕ, Measurable H ∧ (∀ m, IsCompact {x | H x ≤ m}) ∧
      ∀ N : ℕ, observationEntropyRate μ (fun x => rightAction x a) (heightClip H N) < ε := by
  obtain ⟨H,hH,hK,hstep⟩ := exists_compact_height_bounded_step a
  obtain ⟨q,r,hq,hr,hent⟩ := exists_coarse_height_small_entropy μ ha H hH hstep hε
  let J : X n → ℕ := fun x => (H x+r)/q
  refine ⟨J,(measurable_of_countable (fun k : ℕ => (k+r)/q)).comp hH,?_,hent⟩
  intro m
  have hqm : r < q*(m+1) := by nlinarith
  have he : {x | J x ≤ m} = {x | H x ≤ q*(m+1)-1-r} := by
    ext x
    change (H x+r)/q ≤ m ↔ H x ≤ q*(m+1)-1-r
    rw [Nat.le_iff_lt_add_one,Nat.div_lt_iff_lt_mul hq,Nat.mul_comm (m+1) q]
    omega
  rw [he]
  exact hK _

end DukePrimeDegree

end

end OAI
