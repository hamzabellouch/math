import OAI.MeasureTheory.Falconer.Estimates.PacketScaleCombination

namespace OAI

/-! Product counting for a local union carried by globally frozen packets.
The local factor is arbitrary; no local incidence estimate is assumed. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem frozen_packet_card_product {n H M : ℝ}
    (hn : 0 < n) (_hH : 0 ≤ H) (hM : 0 ≤ M)
    (A B F V : Finset (Space 2)) (G : Space 2 → Finset (Space 2))
    (hBA : B ⊆ A) (hB : (B.card:ℝ) ≤ M) (hF : F ⊆ B.biUnion G)
    (hband : ∀ a ∈ A, n ≤ ((G a).card:ℝ) ∧ ((G a).card:ℝ) ≤ 2*n)
    (htotal : (∑ a ∈ A, ((G a).card:ℝ)) ≤ H*(V.card:ℝ)) :
    (A.card:ℝ)*(F.card:ℝ) ≤ 2*H*M*(V.card:ℝ) := by
  have hlocal : (F.card:ℝ) ≤ 2*n*M := by
    calc
      _ ≤ ∑ a ∈ B, ((G a).card:ℝ) := by
        exact_mod_cast (Finset.card_le_card hF).trans Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ B, 2*n := Finset.sum_le_sum fun a ha => (hband a (hBA ha)).2
      _ = 2*n*(B.card:ℝ) := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)
  have hglobal : n*(A.card:ℝ) ≤ H*(V.card:ℝ) := by
    calc
      _ = ∑ _a ∈ A, n := by simp; ring
      _ ≤ ∑ a ∈ A, ((G a).card:ℝ) := Finset.sum_le_sum fun a ha => (hband a ha).1
      _ ≤ _ := htotal
  calc
    _ ≤ (A.card:ℝ)*(2*n*M) := mul_le_mul_of_nonneg_left hlocal (Nat.cast_nonneg _)
    _ = 2*M*(n*(A.card:ℝ)) := by ring
    _ ≤ 2*M*(H*(V.card:ℝ)) := mul_le_mul_of_nonneg_left hglobal (by positivity)
    _ = _ := by ring

end Falconer

end OAI
