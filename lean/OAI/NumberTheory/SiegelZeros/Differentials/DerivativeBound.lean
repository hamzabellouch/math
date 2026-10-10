import OAI.NumberTheory.SiegelZeros.EntireFunctions.Hadamard
import OAI.NumberTheory.SiegelZeros.Selection.RowReplacement
import OAI.NumberTheory.SiegelZeros.Structure.ArchimedeanTheta

namespace OAI

namespace SiegelZeros


noncomputable section
open scoped BigOperators

namespace WeightedTorusJets.W35

theorem eigenvalueMatrix_eq_derivatives {m : ℕ}
    (v : Fin 3 → Fin 4 → ℂ) (a : Fin m → Fin 3 → ℕ)
    (n : Fin m → Fin 4 →₀ ℕ) :
    eigenvalueMatrix (fun k j => W18.eigenvalue (v k) (n j)) a =
      fun i j => MvPolynomial.eval (fun _ => (1 : ℂ))
        (W19.mixedInvariant v (a i) (MvPolynomial.monomial (n j) 1)) := by
  ext i j
  exact (W19.derivative_row_at_one v (a i) (n j)).symm

theorem log_height (N q : ℕ) (hN : 0 < N) (hq : 0 < q) :
    Real.log (8 * (N : ℝ) * Real.sqrt (q : ℝ)) =
      Real.log N + (1 / 2 : ℝ) * Real.log q + Real.log 8 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Real.log_mul (mul_pos (by norm_num) hNp).ne' (Real.sqrt_pos.2 hqp).ne',
    Real.log_mul (by norm_num) hNp.ne', Real.log_sqrt hqp.le]
  ring

theorem embedding_log_det_bound {K : Type*} [Ring K] {m : ℕ} (hm : 0 < m)
    (ν : Fin 3 → K →+* ℂ) (a b : K) (d : ℤ) (q N : ℕ)
    (orders : Fin m → Fin 3 → ℕ) (n : Fin m → Fin 4 → ℕ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hq : 1 ≤ q) (hN : 0 < N) (hd : |(d : ℝ)| ≤ (q : ℝ))
    (hn : ∀ j i, n j i ≤ N)
    (hne : (eigenvalueMatrix (fun k j => ν k (W34.theta a b (n j))) orders).det ≠ 0) :
    Real.log ‖(eigenvalueMatrix (fun k j => ν k (W34.theta a b (n j))) orders).det‖ ≤
      (m : ℝ) / 2 * Real.log m +
      (∑ i, ((orders i 0 + orders i 1 + orders i 2 : ℕ) : ℝ)) *
        (Real.log N + (1 / 2 : ℝ) * Real.log q + Real.log 8) := by
  have hq0 : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq0
  have hB : 0 < 8 * (N : ℝ) * Real.sqrt (q : ℝ) :=
    mul_pos (mul_pos (by norm_num) hNp) (Real.sqrt_pos.2 hqp)
  have h := log_norm_eigenvalueMatrix_det_le hm
    (fun k j => ν k (W34.theta a b (n j))) orders
    (8 * (N : ℝ) * Real.sqrt (q : ℝ)) hB
    (fun k j => W34.embedding_theta_bound (ν k) a b d q N (n j) ha hb hq hd (hn j)) hne
  rwa [log_height N q hN hq0] at h

end WeightedTorusJets.W35

end


end SiegelZeros

end OAI
