import OAI.MeasureTheory.Falconer.Incidence.RoundedBlockIntervals

namespace OAI

/-! Exact length accounting and even scales for the selected block intervals. -/
namespace Falconer
open Regularization

theorem block_interval_length_eq {m B i j : ℕ} (hm : 0 < m) (hB : 0 < B)
    (hji : j ≤ i) {c : ℝ × ℝ}
    (ha : c.1 = (blockDepth (m*B) B i:ℝ)/(m*B:ℕ))
    (hb : c.1+c.2 = (blockDepth (m*B) B j:ℝ)/(m*B:ℕ)) :
    ((blockDepth (m*B) B j-blockDepth (m*B) B i:ℕ):ℝ) = ((m*B:ℕ):ℝ)*c.2 := by
  have hN : ((m*B:ℕ):ℝ) ≠ 0 := (Nat.cast_pos.mpr (Nat.mul_pos hm hB)).ne'
  have ha' := (eq_div_iff hN).mp ha
  have hb' := (eq_div_iff hN).mp hb
  rw [Nat.cast_sub (blockDepth_antitone (m*B) B hji)]
  nlinarith only [ha',hb']

theorem rounded_block_total_depth {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (S : List (ℝ × ℝ)) (I : (ℝ × ℝ) → (ℕ × ℕ))
    (hI : ∀ c ∈ S, (I c).2 ≤ (I c).1 ∧
      (innerProfileCell m c).1 = (blockDepth (m*B) B (I c).1:ℝ)/(m*B:ℕ) ∧
      (innerProfileCell m c).1+(innerProfileCell m c).2 =
        (blockDepth (m*B) B (I c).2:ℝ)/(m*B:ℕ)) :
    (S.map fun c => ((blockDepth (m*B) B (I c).2-blockDepth (m*B) B (I c).1:ℕ):ℝ)).sum =
      ((m*B:ℕ):ℝ)*(S.map fun c => (innerProfileCell m c).2).sum := by
  induction S with
  | nil => simp
  | cons c S ih =>
    have hc := hI c (by simp)
    have ht := ih (fun d hd => hI d (by simp [hd]))
    simp only [List.map_cons,List.sum_cons]
    rw [block_interval_length_eq hm hB hc.1 hc.2.1 hc.2.2,ht]
    ring

theorem exists_half_block_length {m B i j : ℕ} (hB : Even B) :
    ∃ n : ℕ, blockDepth (m*B) B j-blockDepth (m*B) B i = 2*n := by
  have sub_even {a b : ℕ} (ha : Even a) (hb : Even b) : Even (a-b) := by
    rcases le_total b a with h | h
    · exact (Nat.even_sub h).2 ⟨fun _ => hb,fun _ => ha⟩
    · simp [Nat.sub_eq_zero_of_le h]
  have hN : Even (m*B) := hB.mul_left m
  have hi : Even (blockDepth (m*B) B i) := by
    dsimp [blockDepth]
    exact sub_even hN (hB.mul_left i)
  have hj : Even (blockDepth (m*B) B j) := by
    dsimp [blockDepth]
    exact sub_even hN (hB.mul_left j)
  obtain ⟨n,hn⟩ := sub_even hj hi
  exact ⟨n,by omega⟩

end Falconer

end OAI
