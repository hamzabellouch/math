import OAI.Combinatorics.DiscreteConvexity.Bins
import OAI.Combinatorics.DiscreteConvexity.ElementaryCovering
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# From actual dyadic weights to a containment cover

The only inputs are the two weight inequalities.  All bins, their finite
index set, their covers, and the final union are constructed in the proof.
-/

open scoped BigOperators

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem weights_small {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (A : Family α) (W : Finset α → ℝ) (hW : ∀ U, 0 ≤ W U)
    (hglobal : (∑ U : Finset α, q ^ U.card * W U) ≤ 1)
    (hlower : ∀ S ∈ A,
      (1 / 2 : ℝ) ^ 32 ≤ ∑ U ∈ S.powerset.erase ∅, (W U) ^ 16) :
    Small (q / (2 : ℝ) ^ 70) A := by
  classical
  let ρ : ℝ := q / (2 : ℝ) ^ 70
  let B := occupiedWeightBins W
  have hρ0 : 0 < ρ := div_pos hq0 (pow_pos (by norm_num) _)
  have hρq : ρ ≤ q := div_le_self hq0.le (one_le_pow₀ (by norm_num))
  have hρ1 : ρ < 1 := hρq.trans_lt hq1
  have hB : ∀ b ∈ B, 1 ≤ b.1 ∧ 64 * b.1 ≤ b.2 :=
    fun _ hb => occupiedWeightBins_bounds hb
  have each : ∀ b : ℕ × ℕ, ∃ G : Family α, b ∈ B →
      Covers G (Covering.denseFamily (weightBin W b) (2 ^ (12 * b.2))) ∧
      cost ρ G ≤ 3 * (1 / 2 : ℝ) ^ b.2 := by
    intro b
    by_cases hb : b ∈ B
    · have hbnd := hB b hb
      obtain ⟨G, hcover, hcost⟩ := Covering.elementary_covering
        (weightBin W b) ρ b.1 b.2 hρ0 hρ1
        (fun U hU => weightBin_card hU) hbnd.1
        (by omega) (by omega) (weightBin_cost_bound hq0 hW hglobal b)
      refine ⟨G, fun _ => ⟨hcover, ?_⟩⟩
      simpa only [one_div, inv_pow] using hcost
    · exact ⟨∅, fun h => False.elim (hb h)⟩
  let G : (ℕ × ℕ) → Family α := fun b => Classical.choose (each b)
  have hG : ∀ b ∈ B,
      Covers (G b) (Covering.denseFamily (weightBin W b) (2 ^ (12 * b.2))) ∧
      cost ρ (G b) ≤ 3 * (1 / 2 : ℝ) ^ b.2 :=
    fun b hb => Classical.choose_spec (each b) hb
  let C : Family α := largeWeightFamily W ∪ B.biUnion G
  have hcost : cost ρ C ≤ 1 / 2 := by
    have hsum : (∑ b ∈ B, cost ρ (G b)) < 1 / 4 :=
      (Finset.sum_le_sum (fun b hb => (hG b hb).2)).trans_lt
        (finite_bin_cost_lt_quarter B hB)
    have hlarge : cost ρ (largeWeightFamily W) ≤ 1 / 64 :=
      largeWeightFamily_cost_le hq0.le hW hglobal
    have htotal := (cost_union_le hρ0.le (largeWeightFamily W) (B.biUnion G)).trans
      (add_le_add le_rfl (cost_biUnion_le hρ0.le B G))
    change cost ρ (largeWeightFamily W ∪ B.biUnion G) ≤ 1 / 2
    linarith
  refine ⟨C, ?_, hcost⟩
  intro S hS
  by_contra hcovered
  have hnone : ∀ I ∈ C, ¬ I ⊆ S := by
    intro I hI hIS
    exact hcovered ⟨I, hI, hIS⟩
  have hlarge : ∀ U ∈ largeWeightFamily W, ¬ U ⊆ S := by
    intro U hU
    exact hnone U (Finset.mem_union_left _ hU)
  have hcount : ∀ b ∈ B,
      ((weightBin W b).filter (fun U => U ⊆ S)).card ≤ 2 ^ (12 * b.2) := by
    intro b hb
    have hnot : ¬ S ∈ Covering.denseFamily (weightBin W b) (2 ^ (12 * b.2)) := by
      intro hdense
      obtain ⟨I, hI, hIS⟩ := (hG b hb).1 S hdense
      exact hnone I (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, hb, hI⟩)) hIS
    have hlt : ((weightBin W b).filter (fun U => U ⊆ S)).card < 2 ^ (12 * b.2) :=
      lt_of_not_ge (fun h => hnot (Covering.mem_denseFamily.mpr h))
    exact hlt.le
  have hupper : (∑ U ∈ S.powerset.erase ∅, (W U) ^ 16) < (1 / 2 : ℝ) ^ 32 := by
    calc
      _ ≤ ∑ b ∈ B, ∑ U ∈ (weightBin W b).filter (fun U => U ⊆ S), (W U) ^ 16 :=
        subset_power_sum_le_bins hW S hlarge
      _ ≤ ∑ b ∈ B, (1 / 2 : ℝ) ^ (4 * b.2) :=
        Finset.sum_le_sum (fun b hb => weightBin_power_sum_le hW S b (hcount b hb))
      _ < (1 / 2 : ℝ) ^ 32 := finite_bin_power_lt_threshold B hB
  exact (not_lt_of_ge (hlower S hS)) hupper

end TalagrandDiscreteConvexity

end OAI
