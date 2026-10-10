import OAI.Combinatorics.PerfectMatching.SizeBounds

namespace OAI

section

namespace BinaryMatching.Algorithm
open Finset

def tau (G : Input) : ℕ := G.n+B G+1

def Q (G : Input) : ℕ := D₀ G*2^(K G.n)

lemma tau_pos (G : Input) : 0<tau G := by unfold tau; omega
lemma order_le_tau (G : Input) : G.n≤tau G := by unfold tau; omega
lemma B_le_tau (G : Input) : B G≤tau G := by unfold tau; omega

lemma K_le_q (n : ℕ) : K n≤q n :=
  Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_two_pow_self))

lemma q_le_tau_sq (G : Input) : q G.n≤(tau G)^2 :=
  q_le_square.trans (Nat.pow_le_pow_left (order_le_tau G) 2)

lemma tau_pow_mono (G : Input) {i j : ℕ} (h : i≤j) : (tau G)^i≤(tau G)^j :=
  Nat.pow_le_pow_right (tau_pos G) h

lemma K_L_bound (G : Input) : K G.n+L G≤101*(tau G)^3 := by
  have hk : K G.n≤(tau G)^3 :=
    (K_le_q G.n).trans ((q_le_tau_sq G).trans (tau_pow_mono G (by omega)))
  change K G.n+100*(tau G)^3≤_
  omega

lemma A₀_bound (G : Input) : 2+A₀ G.n≤12*(tau G)^2 := by
  have hn := Nat.pow_le_pow_left (order_le_tau G) 2
  have ht : 1≤(tau G)^2 := one_le_pow₀ (tau_pos G)
  unfold A₀
  omega

lemma M₀_bound (G : Input) : M₀ G≤1212*(tau G)^7 := by
  calc
    _ ≤ (tau G)^2*(101*(tau G)^3)*(12*(tau G)^2) :=
      Nat.mul_le_mul (Nat.mul_le_mul (q_le_tau_sq G) (K_L_bound G)) (A₀_bound G)
    _ = _ := by ring

lemma K_L_M_bound (G : Input) : K G.n+L G+M₀ G≤1313*(tau G)^7 := by
  have hk := (K_L_bound G).trans (Nat.mul_le_mul_left 101 (tau_pow_mono G (by omega : 3≤7)))
  have hm := M₀_bound G
  omega

lemma D₀_bound (G : Input) : D₀ G≤1313^2*(tau G)^16 := by
  calc
    _ ≤ (tau G)^2*(1313*(tau G)^7)^2 :=
      Nat.mul_le_mul (q_le_tau_sq G) (Nat.pow_le_pow_left (K_L_M_bound G) 2)
    _ = _ := by ring

lemma iterations_bound (G : Input) : q G.n*D₀ G≤1313^2*(tau G)^18 := by
  calc
    _ ≤ (tau G)^2*(1313^2*(tau G)^16) := Nat.mul_le_mul (q_le_tau_sq G) (D₀_bound G)
    _ = _ := by ring

lemma pow_K_bound (n : ℕ) (hn : 2≤n) : 2^(K n)≤2*q n := by
  have hq := q_pos hn
  by_cases he : q n=1
  · simp [K,he]
  · have hq' : 1<q n := by omega
    have hk : 0<K n := by
      unfold K
      rw [Nat.pos_iff_ne_zero]
      intro h
      have hh := Nat.le_pow_clog (by omega : 1<2) (q n)
      rw [h] at hh
      simp at hh
      omega
    have hh := Nat.pow_pred_clog_lt_self (by omega : 1<2) hq'
    change 2^(K n-1)<q n at hh
    calc
      _ = 2^(K n-1)*2 := by rw [←pow_succ]; congr 1; omega
      _ ≤ q n*2 := Nat.mul_le_mul_right _ hh.le
      _ = _ := by omega

lemma Q_bound (G : Input) (hn : 2≤G.n) : Q G≤2*1313^2*(tau G)^18 := by
  calc
    _ ≤ (1313^2*(tau G)^16)*(2*(tau G)^2) :=
      Nat.mul_le_mul (D₀_bound G) ((pow_K_bound G.n hn).trans (Nat.mul_le_mul_left 2 (q_le_tau_sq G)))
    _ = _ := by ring

lemma tau_input_bound (G : Input) (hguard : G.n≤(covered G).card) :
    tau G≤3*inputLength G+1 := by
  have hn := hguard.trans ((covered_card_le_records G).trans
    (Nat.mul_le_mul_left 2 (records_length_le_input G)))
  have hb := B_le_input G
  unfold tau
  omega

end BinaryMatching.Algorithm
end

end OAI
