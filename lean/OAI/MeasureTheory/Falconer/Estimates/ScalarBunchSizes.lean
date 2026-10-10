import OAI.MeasureTheory.Falconer.Measures.ScalarBunchProducts

namespace OAI

/-! Choosing group sizes from the greedy bunch lengths. A threshold 2P
 gives groups of size 2^(P length), with a closed formula for total gain. -/
namespace Falconer

def scalarBunchGroup (P : ℕ) (b : ScalarBunch) : ℕ := 2^(P*(b.stop-b.start))

 theorem ScalarBunch.length_pos (b : ScalarBunch) : 0 < b.stop-b.start := by
  have h1 := b.start_lt_cut
  have h2 := b.cut_le_stop
  omega

 theorem scalar_bunch_group_large {P : ℕ} (hP : 18 ≤ P) (b : ScalarBunch) :
    83521 ≤ scalarBunchGroup P b := by
  have hx : 18 ≤ P*(b.stop-b.start) := by
    have hh := Nat.mul_le_mul_left P (show 1 ≤ b.stop-b.start from b.length_pos)
    omega
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hx
  exact (by norm_num : 83521 ≤ 2^18).trans hpow

 theorem scalar_bunch_group_room (w : ℕ → ℕ) {P : ℕ} (hP : 2 ≤ P) (b : ScalarBunch)
    (hgood : ScalarBunchGood (fun i => (w i:ℝ)) (2*(P:ℝ)) b) :
    2*scalarBunchGroup P b ≤ 2^(∑ i ∈ Finset.Ico b.start b.cut, w i) := by
  have hx : 2 ≤ P*(b.stop-b.start) := by
    have hh := Nat.mul_le_mul_left P (show 1 ≤ b.stop-b.start from b.length_pos)
    omega
  have hxR : (2:ℝ) ≤ (P:ℝ)*((b.stop-b.start:ℕ):ℝ) := by exact_mod_cast hx
  have hr := hgood.retained
  have hs : ((P*(b.stop-b.start)+1:ℕ):ℝ) ≤
      ((∑ i ∈ Finset.Ico b.start b.cut, w i):ℝ) := by
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one]
    nlinarith
  have hsN : P*(b.stop-b.start)+1 ≤ ∑ i ∈ Finset.Ico b.start b.cut, w i := by exact_mod_cast hs
  calc
    2*scalarBunchGroup P b = 2^(P*(b.stop-b.start)+1) := by
      simp only [scalarBunchGroup,pow_succ]
      omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hsN

 theorem ScalarBunchChain.group_log_sum {top lo P : ℕ} {bs : List ScalarBunch}
    (h : ScalarBunchChain top lo bs) :
    (bs.map (fun b => Real.log (scalarBunchGroup P b:ℝ))).sum =
      (P:ℝ)*((top-lo:ℕ):ℝ)*Real.log 2 := by
  induction h with
  | nil n => simp
  | @cons b lo bs h ih =>
    have he : ((b.stop-lo:ℕ):ℝ) = ((b.stop-b.start:ℕ):ℝ)+((b.start-lo:ℕ):ℝ) := by
      have hlo := h.start_le
      have h1 := b.start_lt_cut
      have h2 := b.cut_le_stop
      exact_mod_cast (show b.stop-lo = (b.stop-b.start)+(b.start-lo) by omega)
    simp only [List.map_cons,List.sum_cons]
    rw [ih]
    simp only [scalarBunchGroup,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_mul]
    rw [he]
    ring

end Falconer

end OAI
