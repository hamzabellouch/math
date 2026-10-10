import OAI.Analysis.LipschitzEquivalence.CauchyReduction

namespace OAI

universe uE uF uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped BigOperators

variable {E : Type uE} [AddCommGroup E] [Module ℝ E]

def dyadicMean (u : ℕ → E) : ℕ → ℕ → E
  | 0, k => u k
  | n+1, k => (1/2 : ℝ) • (dyadicMean u n k + dyadicMean u n (k+2^n))

@[simp] theorem dyadicMean_zero (u : ℕ → E) (k : ℕ) : dyadicMean u 0 k = u k := rfl

@[simp] theorem dyadicMean_succ (u : ℕ → E) (n k : ℕ) :
    dyadicMean u (n+1) k = (1/2 : ℝ) • (dyadicMean u n k + dyadicMean u n (k+2^n)) := rfl

variable {F : Type uF} [AddCommGroup F] [Module ℝ F]

theorem map_dyadicMean (T : E →ₗ[ℝ] F) (u : ℕ → E) (n k : ℕ) :
    T (dyadicMean u n k) = dyadicMean (fun i => T (u i)) n k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp only [dyadicMean_succ, map_smul, map_add, ih]

theorem dyadicMean_le (u : ℕ → ℝ) (n k : ℕ) {b : ℝ}
    (h : ∀ i, k ≤ i → i < k+2^n → u i ≤ b) : dyadicMean u n k ≤ b := by
  induction n generalizing k with
  | zero => exact h k le_rfl (by simp)
  | succ n ih =>
    have hpow : (2 : ℕ)^(n+1) = 2^n+2^n := by omega
    have hp : 0 < (2 : ℕ)^n := pow_pos (by norm_num) n
    have h₁ : dyadicMean u n k ≤ b := ih k (fun i hi hi' => h i hi (by omega))
    have h₂ : dyadicMean u n (k+2^n) ≤ b :=
      ih (k+2^n) (fun i hi hi' => h i (by omega) (by omega))
    simp only [dyadicMean_succ, smul_eq_mul]
    linarith

theorem le_dyadicMean (u : ℕ → ℝ) (n k : ℕ) {b : ℝ}
    (h : ∀ i, k ≤ i → i < k+2^n → b ≤ u i) : b ≤ dyadicMean u n k := by
  induction n generalizing k with
  | zero => exact h k le_rfl (by simp)
  | succ n ih =>
    have hpow : (2 : ℕ)^(n+1) = 2^n+2^n := by omega
    have hp : 0 < (2 : ℕ)^n := pow_pos (by norm_num) n
    have h₁ : b ≤ dyadicMean u n k := ih k (fun i hi hi' => h i hi (by omega))
    have h₂ : b ≤ dyadicMean u n (k+2^n) :=
      ih (k+2^n) (fun i hi hi' => h i (by omega) (by omega))
    simp only [dyadicMean_succ, smul_eq_mul]
    linarith

theorem dyadic_energy_bound (Q : E → ℝ)
    (hmid : ∀ x y, Q ((1/2 : ℝ) • (x+y)) = (Q x+Q y)/2-Q (x-y)/4)
    (u : ℕ → E) (N : ℕ) (C ε : ℝ)
    (hu : ∀ k < N, Q (u k) ≤ C)
    (hgap : ∀ n k, k+2^(n+1) ≤ N →
      ε ≤ Q (dyadicMean u n k-dyadicMean u n (k+2^n)))
    (n k : ℕ) (hk : k+2^n ≤ N) :
    Q (dyadicMean u n k) ≤ C-(n : ℝ)*ε/4 := by
  induction n generalizing k with
  | zero => simpa using hu k (by simpa using hk)
  | succ n ih =>
    have hpow : (2 : ℕ)^(n+1) = 2^n+2^n := by omega
    have hp : 0 < (2 : ℕ)^n := pow_pos (by norm_num) n
    have h₁ := ih k (by omega)
    have h₂ := ih (k+2^n) (by omega)
    have hg := hgap n k hk
    rw [dyadicMean_succ, hmid]
    push_cast
    linarith

theorem exists_small_dyadic_difference (Q : E → ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (hmid : ∀ x y, Q ((1/2 : ℝ) • (x+y)) = (Q x+Q y)/2-Q (x-y)/4)
    (u : ℕ → E) {C ε : ℝ} (_hε : 0 < ε) (d : ℕ) (hd : 4*C < (d : ℝ)*ε)
    (hu : ∀ k < 2^d, Q (u k) ≤ C) :
    ∃ n k, n < d ∧ k+2^(n+1) ≤ 2^d ∧
      Q (dyadicMean u n k-dyadicMean u n (k+2^n)) < ε := by
  by_contra! h
  have hgap : ∀ n k, k+2^(n+1) ≤ 2^d →
      ε ≤ Q (dyadicMean u n k-dyadicMean u n (k+2^n)) := by
    intro n k hk
    have hn : n < d := by
      have hp : 2^(n+1) ≤ 2^d := by omega
      have : n+1 ≤ d := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hp
      omega
    exact h n k hn hk
  have hb := dyadic_energy_bound Q hmid u (2^d) C ε hu hgap d 0 (by simp)
  have hnonneg := hQ (dyadicMean u d 0)
  linarith

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem hilbert_midpoint_energy (x y : H) :
    ‖(1/2 : ℝ) • (x+y)‖^2 = (‖x‖^2+‖y‖^2)/2-‖x-y‖^2/4 := by
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  rw [mul_pow, norm_add_sq_real, norm_sub_sq_real]
  ring

theorem hilbert_small_ordered_blocks (u : ℕ → H) {R ε : ℝ} (hε : 0 < ε)
    (d : ℕ) (hd : 4*R^2 < (d : ℝ)*ε^2)
    (hu : ∀ k < 2^d, ‖u k‖ ≤ R) :
    ∃ n k, n < d ∧ k+2^(n+1) ≤ 2^d ∧
      ‖dyadicMean u n k-dyadicMean u n (k+2^n)‖ < ε := by
  obtain ⟨n,k,hn,hk,hsmall⟩ := exists_small_dyadic_difference
    (fun x : H => ‖x‖^2) (fun _ => sq_nonneg _) hilbert_midpoint_energy u
    (sq_pos_of_pos hε) d hd (fun k hk => sq_le_sq₀ (norm_nonneg _) (le_trans (norm_nonneg _) (hu k hk)) |>.mpr (hu k hk))
  exact ⟨n,k,hn,hk,by nlinarith [norm_nonneg (dyadicMean u n k-dyadicMean u n (k+2^n))]⟩

end LipschitzCounterexample.CompactWSC
end

end OAI
