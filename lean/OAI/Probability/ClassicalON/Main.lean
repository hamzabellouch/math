import OAI.Probability.ClassicalON.BlockReduction

namespace OAI

noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators Classical
namespace ClassicalON

theorem correlation_eq_freeSpinMean (n : ℕ) (G : LatticeGraph) (b : G.edges → ℝ) (x y : G.vertices) :
    correlation n G b x y=freeSpinMean n (fun e : G.edges => e.val.1) (fun e => e.val.2) b
      (fun s => ⟪(s x).val,(s y).val⟫_ℝ) := by
  unfold correlation partition interaction referenceLaw freeSpinMean weightedMean freeSpinEnergy freeSpinReference
  congr 1
  apply integral_congr_ae
  filter_upwards with s
  exact mul_comm _ _

theorem main : ExponentialDecay := by
  intro n hn β hβ
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  let : NeZero (3+k) := ⟨by omega⟩
  obtain ⟨m,hm,hexp⟩ := LatticeGraph.connection_exponential β hβ.le
  refine ⟨(3+k:ℕ)*4,m,hm,?_⟩
  intro G b hb x y
  have hthree (c : G.edges → ℝ) (hc : ∀ e,0 ≤ c e ∧ c e ≤ b e) :
      0 ≤ freeSpinMean 3 (fun e : G.edges => e.val.1) (fun e => e.val.2) c (firstSpinProduct x y) ∧
      freeSpinMean 3 (fun e : G.edges => e.val.1) (fun e => e.val.2) c (firstSpinProduct x y) ≤
        4*Real.exp (-m*siteDistance x.val y.val) := by
    have hfirst := firstSpinMean_bounds (fun e : G.edges => e.val.1) (fun e => e.val.2) c
      (fun e => (hc e).1) x y
    exact ⟨hfirst.1,hfirst.2.trans (hexp G c (fun e => ⟨(hc e).1,(hc e).2.trans (hb e).2⟩) x y)⟩
  have hbound := coordinateSpinMean_block_bounds k (fun e : G.edges => e.val.1) (fun e => e.val.2) b
    (fun e => (hb e).1) x y (4*Real.exp (-m*siteDistance x.val y.val)) hthree
  rw [correlation_eq_freeSpinMean,innerSpinMean_eq_coordinate (3+k)
    (fun e : G.edges => e.val.1) (fun e => e.val.2) b ⟨0,by omega⟩ x y]
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) hbound.1
  · calc
      _ ≤ (3+k:ℕ)*(4*Real.exp (-m*siteDistance x.val y.val)) :=
        mul_le_mul_of_nonneg_left hbound.2 (Nat.cast_nonneg _)
      _ = _ := by ring

end ClassicalON

end

end OAI
