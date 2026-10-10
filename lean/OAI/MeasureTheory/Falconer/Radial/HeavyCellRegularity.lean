import OAI.MeasureTheory.Falconer.Estimates.LocalPacketRegularity
import OAI.MeasureTheory.Falconer.Estimates.RegularCoarseCells

namespace OAI

/-! Heavy-cell selection supplies the local point regularity used in the
coarse-direction projection argument, with the complete loss displayed. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem heavy_cells_local_regular {δ Δ t K J : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hK : 0 ≤ K) (hJ : 0 ≤ J)
    (P C : Finset (Space 2)) (S : Space 2 → Finset (Space 2)) (k : ℕ)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hS : ∀ c ∈ C, S c ⊆ P ∧ 2^k ≤ (S c).card ∧ (S c).card < 2^(k+1))
    (hmass : (P.card:ℝ) ≤ J*(∑ c ∈ C, ((S c).card:ℝ))) :
    ∀ c ∈ C, (S c).Nonempty ∧
      NormalizedFiniteBallBound (δ/Δ) t
        ((K*(2*J*(C.card:ℝ)))*Δ^t) ((S c).image (localPacketPoint Δ (c 0) (c 1))) := by
  have hsum : (∑ c ∈ C, ((S c).card:ℝ)) ≤ (2*(2:ℝ)^k)*(C.card:ℝ) := by
    calc
      _ ≤ ∑ _c ∈ C, 2*(2:ℝ)^k := Finset.sum_le_sum fun c hc => by
        have hh : ((S c).card:ℝ) < (2:ℝ)^(k+1) := by exact_mod_cast (hS c hc).2.2
        simpa only [pow_succ,mul_comm] using hh.le
      _ = _ := by simp; ring
  intro c hc
  have hlo : (2:ℝ)^k ≤ ((S c).card:ℝ) := by exact_mod_cast (hS c hc).2.1
  have hSc : 0 < ((S c).card:ℝ) := (by positivity : (0:ℝ) < 2^k).trans_le hlo
  have hsize : (P.card:ℝ) ≤ (2*J*(C.card:ℝ))*((S c).card:ℝ) := by
    calc
      _ ≤ J*(∑ c ∈ C, ((S c).card:ℝ)) := hmass
      _ ≤ J*((2*(2:ℝ)^k)*(C.card:ℝ)) := mul_le_mul_of_nonneg_left hsum hJ
      _ = (2*J*(C.card:ℝ))*(2:ℝ)^k := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)
  exact ⟨Finset.card_pos.mp (Nat.cast_pos.mp hSc),local_packet_subset_regular
    hδ hΔ hΔ1 hK (c 0) (c 1) P (S c) (hS c hc).1 hsize hPball⟩

end Falconer

end OAI
