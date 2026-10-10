import OAI.MeasureTheory.Falconer.Angular.AngularTransportBounds

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

noncomputable def scaledAngularTransportCost (Q : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | n+1, m => ∑ k ∈ Finset.range (m+2),
      ((m+1).choose k : ℝ) * Q k * scaledAngularTransportCost Q n (m+1-k)

theorem scaledAngularTransportCost_nonneg {Q : ℕ → ℝ} (hQ : ∀ k, 0 ≤ Q k)
    (n m : ℕ) : 0 ≤ scaledAngularTransportCost Q n m := by
  induction n generalizing m with
  | zero => exact zero_le_one
  | succ n ih =>
    exact Finset.sum_nonneg (fun k _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hQ k)) (ih _))

theorem angularTransportIterate_scaled_bound {q f : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f)
    {Q : ℕ → ℝ} (hQ : ∀ k, 0 ≤ Q k) {C U D : ℝ}
    (hC : 0 ≤ C) (hU : 0 ≤ U) (hD : 0 ≤ D) (n m : ℕ) (x : ℝ)
    (hbq : ∀ k ≤ n+m, ‖iteratedDeriv k q x‖ ≤ Q k * U * D^k)
    (hbf : ∀ k ≤ n+m, ‖iteratedDeriv k f x‖ ≤ C * D^k) :
    ‖iteratedDeriv m (angularTransportIterate q n f) x‖ ≤
      scaledAngularTransportCost Q n m * C * U^n * D^(n+m) := by
  induction n generalizing m with
  | zero => simpa [angularTransportIterate, scaledAngularTransportCost] using hbf m (by omega)
  | succ n ih =>
    have hqn : ContDiffAt ℝ (m+1 : ℕ) q x :=
      (hq.of_le (WithTop.coe_le_coe.mpr (show ((m+1 : ℕ) : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    have hfn : ContDiffAt ℝ (m+1 : ℕ) (angularTransportIterate q n f) x :=
      ((angularTransportIterate_contDiff hq hf n).of_le
        (WithTop.coe_le_coe.mpr (show ((m+1 : ℕ) : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    change ‖iteratedDeriv m (deriv (fun y => q y * angularTransportIterate q n f y)) x‖ ≤ _
    rw [← iteratedDeriv_succ', iteratedDeriv_fun_mul hqn hfn]
    change ‖_‖ ≤ (∑ k ∈ Finset.range (m+2), _) * C * U^(n+1) * D^(n+1+m)
    simp only [Finset.sum_mul]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k ≤ m+1 := by simp only [Finset.mem_range] at hk; omega
    have hl : n+(m+1-k) ≤ n+1+m := by omega
    have hb := ih (m+1-k) (fun j hj => hbq j (hj.trans hl))
      (fun j hj => hbf j (hj.trans hl))
    simp only [norm_mul, Complex.norm_natCast]
    calc
      _ ≤ ((m+1).choose k : ℝ) * (Q k * U * D^k) *
          (scaledAngularTransportCost Q n (m+1-k) * C * U^n * D^(n+(m+1-k))) := by
        apply mul_le_mul_of_nonneg
        · exact mul_le_mul_of_nonneg_left (hbq k (by omega)) (Nat.cast_nonneg _)
        · exact hb
        · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
        · exact mul_nonneg
            (mul_nonneg (mul_nonneg (scaledAngularTransportCost_nonneg hQ _ _) hC)
              (pow_nonneg hU _)) (pow_nonneg hD _)
      _ = _ := by
        have he : k+(n+(m+1-k)) = n+1+m := by omega
        rw [pow_succ]
        calc
          _ = ((m+1).choose k : ℝ) * Q k * scaledAngularTransportCost Q n (m+1-k) *
              C * (U^n * U) * (D^k * D^(n+(m+1-k))) := by ring
          _ = _ := by rw [← pow_add, he]

end PlanarFalconer

end OAI
