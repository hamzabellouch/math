import Mathlib
import OAI.Combinatorics.KMedian.Expanders.WalkMoments
import OAI.Combinatorics.KMedian.Expanders.WalkSegments

namespace OAI

section Inline_PCPStopped

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace Stopped
variable (t : ℕ)
def length : (n : ℕ) → (Fin n → Fin (t+1)) → ℕ
  | 0, _ => 0
  | n+1, c => if c 0 = 0 then 0 else 1 + length n (fun i => c i.succ)

theorem length_le (n : ℕ) (c : Fin n → Fin (t+1)) : length t n c ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold length
    split_ifs
    · omega
    · have := ih (fun i => c i.succ); omega

@[simp] theorem length_cons (n : ℕ) (d : Fin (t+1)) (c : Fin n → Fin (t+1)) :
    length t (n+1) (Fin.cons d c) = if d=0 then 0 else 1+length t n c := by
  simp [length]

noncomputable def survival : ℝ := (t:ℝ)/(t+1)
noncomputable def stopping : ℝ := 1/(t+1)

theorem survival_nonneg : 0 ≤ survival t := div_nonneg (Nat.cast_nonneg _) (by positivity)
theorem stopping_nonneg : 0 ≤ stopping t := by unfold stopping; positivity
theorem survival_add_stopping : survival t + stopping t = 1 := by
  unfold survival stopping
  have hn : (t:ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem coin_expect (a b : ℝ) :
    (𝔼 d : Fin (t+1), if d=0 then a else b) = stopping t * a + survival t * b := by
  classical
  rw [Fintype.expect_eq_sum_div_card, Fin.sum_univ_succ]
  simp only [ite_true, Fin.succ_ne_zero, ite_false, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold survival stopping
  push_cast
  ring

theorem expectation (n : ℕ) (H : ℕ → ℝ) :
    (𝔼 c : Fin n → Fin (t+1), H (length t n c)) =
      (∑ k ∈ range n, stopping t * survival t ^ k * H k) + survival t ^ n * H n := by
  induction n generalizing H with
  | zero => simp [length]
  | succ n ih =>
    rw [expect_word_succ]
    simp_rw [length_cons]
    have he (d : Fin (t+1)) :
        (𝔼 c : Fin n → Fin (t+1), H (if d=0 then 0 else 1+length t n c)) =
        if d=0 then H 0 else 𝔼 c : Fin n → Fin (t+1), H (1+length t n c) := by
      by_cases hd : d=0 <;> simp [hd]
    simp_rw [he]
    rw [coin_expect,ih (fun k => H (1+k)),sum_range_succ']
    simp only [pow_zero,mul_one,pow_succ]
    rw [mul_add, mul_sum]
    have hs : (∑ k ∈ range n, survival t * (stopping t * survival t ^ k * H (1+k))) =
        ∑ k ∈ range n, stopping t * (survival t ^ k * survival t) * H (k+1) := by
      apply sum_congr rfl
      intro k _
      rw [Nat.add_comm 1 k]
      ring
    rw [hs,Nat.add_comm 1 n]
    ring

theorem weights_sum (n : ℕ) :
    (∑ k ∈ range n, stopping t * survival t ^ k) + survival t ^ n = 1 := by
  simpa only [mul_one,Fintype.expect_const] using (expectation t n (fun _ => 1)).symm

end Stopped

namespace PortGraph.Walk
variable {V D : Type} [Fintype V] [Fintype D] [Nonempty D]
variable {G : PortGraph V D}

theorem prefix_expect (n m : ℕ) (f : G.Walk n → ℝ) :
    (𝔼 p : G.Walk (n+m), f (p.segment 0 n (by omega))) = 𝔼 p : G.Walk n, f p := by
  have h := Fintype.expect_equiv (splitEquiv (G := G) n m)
    (fun p : G.Walk (n+m) => f (p.segment 0 n (by omega)))
    (fun z : G.Walk n × (Fin m → D) => f z.1) (fun _ => rfl)
  rw [h,expect_prod]
  simp only [Fintype.expect_const]

theorem prefix_expect_le (n cap : ℕ) (hn : n ≤ cap) (f : G.Walk n → ℝ) :
    (𝔼 p : G.Walk cap, f (p.segment 0 n (by omega))) = 𝔼 p : G.Walk n, f p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact prefix_expect n m f

theorem stopped_expect (t cap : ℕ) (F : (n : ℕ) → G.Walk n → ℝ) :
    (𝔼 c : Fin cap → Fin (t+1), 𝔼 p : G.Walk cap,
      F (Stopped.length t cap c) (p.segment 0 (Stopped.length t cap c)
        (by have := Stopped.length_le t cap c; omega))) =
    (∑ k ∈ range cap, Stopped.stopping t * Stopped.survival t ^ k *
      (𝔼 p : G.Walk k, F k p)) + Stopped.survival t ^ cap * (𝔼 p : G.Walk cap, F cap p) := by
  calc
    _ = 𝔼 c : Fin cap → Fin (t+1), 𝔼 p : G.Walk (Stopped.length t cap c),
        F (Stopped.length t cap c) p := by
      apply expect_congr rfl
      intro c _
      exact prefix_expect_le _ _ (Stopped.length_le t cap c) _
    _ = _ := Stopped.expectation t cap (fun n => 𝔼 p : G.Walk n, F n p)

end PortGraph.Walk
end MetricKMedian.PCP

end Inline_PCPStopped

end OAI
