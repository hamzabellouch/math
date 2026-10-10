import OAI.Combinatorics.ContingencyTables.Rooted.RootedTreeMarginal
import OAI.Combinatorics.ContingencyTables.Rooted.TreeMarginalBounds

namespace OAI

/-! # Selected-root physical tree interpolation after the equality limit -/

namespace ContingencyTables.RootedTreeMarginal

open scoped BigOperators Classical Topology
open Filter CompanionFactorialApplication ForestPenaltyApplication
open LargePairEnumeration BalancedFamily BalancedBox EqualitySoftening RowColumnPenalties
open IntegerWeightedTransport
open TreeMarginalSignature (cellWidth otherWidths coordinateEquiv other_card_le_full)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem scalar_soft_le_two_pow (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha L : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hL : 0 ≤ L) (hW : 20*A.d ≤ A.W) (B K : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hK : 2*B ≤ K) (k : ℕ) :
    scalarSoft A R alpha L t k ≤ (2:ℝ)^K := by
  have hcard := (other_card_le_full A t).trans
    (ForestBoxCardinality.cardinality_le_two_pow A hW B K hB hK)
  have hu := BalancedEnumeration.eliminate_le_card (widths (otherWidths A t))
    (fun z => softenedWeight cellLine (RootedPenalty.rootFlag R) (fun _ => alpha)
      (lineOffset (ForestLiteralCount.lower A.T A.d A.b) (ForestLiteralCount.width A.T A.d A.b) A.r A.c)
      viewSlope (unaryRate A.T A.b alpha) (unaryEll (ForestLiteralCount.lower A.T A.d A.b))
      unarySlope (unaryCap A.b) L (z ∘ (coordinateEquiv A t).symm))
    (by
      intro z
      apply softenedWeight_le_one
      · exact fun _ => ha
      · intro a
        unfold unaryRate
        split_ifs
        · exact div_nonneg ha (Nat.cast_nonneg _)
        · exact le_rfl
      · exact hL)
    (childProfile (cellWidth A t) k)
  exact hu.trans (by exact_mod_cast hcard)

theorem scalar_exact_nonnegative (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (k : ℕ) (hk : k ≤ cellWidth A t) :
    0 ≤ scalarExact A R alpha t k := by
  apply ge_of_tendsto (scalar_tendsto A R alpha t k)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  exact (scalar_positive A R alpha L t ha hL k hk).le

lemma scalar_exact_le_soft (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha L : ℝ) (t : I×J) (k : ℕ) :
    scalarExact A R alpha t k ≤ scalarSoft A R alpha L t k := by
  unfold scalarExact exactMarginal scalarSoft soft
  simp only [BalancedEnumeration.eliminate_eq_sum]
  apply Finset.sum_le_sum
  intro a _
  exact exactWeight_le_softenedWeight _ _ _ _ _ _ _ _ _ _ _

/-- A feasible table attaining the endpoint cell value supplies the
lower bound for finite interpolation through the equality limit. -/
theorem scalar_exact_half_window (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hW : 20*A.d ≤ A.W) (B K k N : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K)
    (hK : 1 ≤ K) (hN : 0 < N) (hkN : k+N ≤ cellWidth A t)
    (hend : 1 ≤ scalarExact A R alpha t (k+N))
    (r : ℕ) (hr : r*K ≤ N) :
    scalarExact A R alpha t k/2 ≤ scalarExact A R alpha t (k+r) := by
  apply le_of_tendsto_of_tendsto ((scalar_tendsto A R alpha t k).div_const 2)
    (scalar_tendsto A R alpha t (k+r))
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  apply positive_sequence_half_window (fun q => scalarSoft A R alpha L t (k+q)) N K hK hN
  · intro q hq
    exact scalar_positive A R alpha L t ha hL _ (by omega)
  · intro q hq
    have hh := scalar_logConcave A R alpha L t ha hL (k+q) (by omega)
    simpa only [Nat.add_assoc] using hh
  · exact hend.trans (scalar_exact_le_soft A R alpha L t (k+N))
  · simpa only [Nat.add_zero] using scalar_soft_le_two_pow A R alpha L t ha hL hW B K hB hBK k
  · exact hr

/-- The same physical half-height estimate when the feasible endpoint
lies to the left of an exterior tree position. -/
theorem scalar_exact_backward_half_window (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hW : 20*A.d ≤ A.W) (B K k N : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K)
    (hK : 1 ≤ K) (hN : 0 < N) (hNk : N ≤ k) (hk : k ≤ cellWidth A t)
    (hend : 1 ≤ scalarExact A R alpha t (k-N)) (r : ℕ) (hr : r*K ≤ N) :
    scalarExact A R alpha t k/2 ≤ scalarExact A R alpha t (k-r) := by
  apply le_of_tendsto_of_tendsto ((scalar_tendsto A R alpha t k).div_const 2)
    (scalar_tendsto A R alpha t (k-r))
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  apply positive_sequence_half_window (fun q => scalarSoft A R alpha L t (k-q)) N K hK hN
  · intro q _
    exact scalar_positive A R alpha L t ha hL _ ((Nat.sub_le _ _).trans hk)
  · intro q hq
    have hqk : q+2 ≤ k := hq.trans hNk
    have hh := scalar_logConcave A R alpha L t ha hL (k-(q+2)) (by omega)
    rw [show k-(q+2)+2=k-q by omega,show k-(q+2)+1=k-(q+1) by omega] at hh
    simpa only [mul_comm] using hh
  · exact hend.trans (scalar_exact_le_soft A R alpha L t (k-N))
  · simpa only [Nat.sub_zero] using scalar_soft_le_two_pow A R alpha L t ha hL hW B K hB hBK k
  · exact hr

/-- The actual physical exterior point has normalized mass at most
2K/b whenever a feasible unit-mass endpoint lies at least b places to
its right, after eliminating all soft parameters. -/
theorem scalar_exact_forward_point_bound (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hW : 20*A.d ≤ A.W) (B K k N b : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K)
    (hK : 0 < K) (hN : 0 < N) (hb : 0 < b) (hbN : b ≤ N)
    (hkN : k+N ≤ cellWidth A t) (hend : 1 ≤ scalarExact A R alpha t (k+N)) :
    scalarExact A R alpha t k/(∑ q ∈ Finset.range (cellWidth A t+1),scalarExact A R alpha t q) ≤
      (2*K:ℝ)/b := by
  have hnonneg : ∀ q,q ≤ cellWidth A t → 0 ≤ scalarExact A R alpha t q :=
    scalar_exact_nonnegative A R alpha t ha
  have hmass := Finset.single_le_sum
    (fun q hq => hnonneg q (by have := Finset.mem_range.mp hq; omega))
    (Finset.mem_range.mpr (show k+N < cellWidth A t+1 by omega))
  have hC : 0 < ∑ q ∈ Finset.range (cellWidth A t+1),scalarExact A R alpha t q := by
    linarith
  apply half_window_mass_bound (scalarExact A R alpha t) (cellWidth A t) k N K b hK hb hbN hkN
    hnonneg hC
  intro r hr
  exact scalar_exact_half_window A R alpha t ha hW B K k N hB hBK hK hN hkN hend r hr

theorem scalar_exact_backward_point_bound (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hW : 20*A.d ≤ A.W) (B K k N b : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K)
    (hK : 0 < K) (hN : 0 < N) (hb : 0 < b) (hbN : b ≤ N)
    (hNk : N ≤ k) (hk : k ≤ cellWidth A t) (hend : 1 ≤ scalarExact A R alpha t (k-N)) :
    scalarExact A R alpha t k/(∑ q ∈ Finset.range (cellWidth A t+1),scalarExact A R alpha t q) ≤
      (2*K:ℝ)/b := by
  let U := cellWidth A t
  let a : ℕ → ℝ := fun q => scalarExact A R alpha t (U-q)
  have hsum : (∑ q ∈ Finset.range (U+1),a q)=
      ∑ q ∈ Finset.range (U+1),scalarExact A R alpha t q := by
    simpa only [a,Nat.add_sub_cancel] using Finset.sum_range_reflect (scalarExact A R alpha t) (U+1)
  have hnonneg : ∀ q,q ≤ U → 0 ≤ a q := by
    intro q _
    exact scalar_exact_nonnegative A R alpha t ha _ (Nat.sub_le _ _)
  have hend' : 1 ≤ a (U-k+N) := by
    change 1 ≤ scalarExact A R alpha t (U-(U-k+N))
    rw [show U-(U-k+N)=k-N by dsimp only [U] at *; omega]
    exact hend
  have hmass := Finset.single_le_sum
    (fun q hq => hnonneg q (by have := Finset.mem_range.mp hq; omega))
    (Finset.mem_range.mpr (show U-k+N < U+1 by dsimp only [U] at *; omega))
  have hC : 0 < ∑ q ∈ Finset.range (U+1),a q := by linarith
  have hp := half_window_mass_bound a U (U-k) N K b hK hb hbN
    (by dsimp only [U] at *; omega) hnonneg hC (by
      intro r hr
      have hrN : r ≤ N := by nlinarith
      change scalarExact A R alpha t (U-(U-k))/2 ≤ scalarExact A R alpha t (U-(U-k+r))
      rw [show U-(U-k)=k by dsimp only [U] at *; omega,
        show U-(U-k+r)=k-r by dsimp only [U] at *; omega]
      exact scalar_exact_backward_half_window A R alpha t ha hW B K k N hB hBK hK hN hNk hk hend r hr)
  change scalarExact A R alpha t (U-(U-k))/(∑ q ∈ Finset.range (U+1),a q) ≤ (2*K:ℝ)/b at hp
  rw [show U-(U-k)=k by dsimp only [U] at *; omega,hsum] at hp
  exact hp

end ContingencyTables.RootedTreeMarginal

end OAI
