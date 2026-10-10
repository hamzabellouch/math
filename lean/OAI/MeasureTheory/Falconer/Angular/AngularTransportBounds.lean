import OAI.MeasureTheory.Falconer.Angular.StationaryChartAmplitude

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

noncomputable def angularTransportIterate (q : ℝ → ℂ) : ℕ → (ℝ → ℂ) → (ℝ → ℂ)
  | 0, f => f
  | n+1, f => deriv (fun x => q x * angularTransportIterate q n f x)

 theorem angularTransportIterate_contDiff {q f : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (angularTransportIterate q n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact (contDiff_infty_iff_deriv.mp (hq.mul ih)).2

 theorem angularTransportIterate_support (q f : ℝ → ℂ) (n : ℕ) :
    tsupport (angularTransportIterate q n f) ⊆ tsupport f := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih => exact tsupport_deriv_subset.trans (tsupport_mul_subset_right.trans ih)

noncomputable def angularTransportCost (q : ℝ → ℂ) : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 1
  | n+1, m, x => ∑ k ∈ Finset.range (m+2),
      ((m+1).choose k:ℝ) * ‖iteratedDeriv k q x‖ * angularTransportCost q n (m+1-k) x

 theorem angularTransportCost_nonneg (q : ℝ → ℂ) (n m : ℕ) (x : ℝ) :
    0 ≤ angularTransportCost q n m x := by
  induction n generalizing m with
  | zero => exact zero_le_one
  | succ n ih =>
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (ih _)

 theorem angularTransportCost_continuous {q : ℝ → ℂ} (hq : ContDiff ℝ ∞ q) (n m : ℕ) :
    Continuous (angularTransportCost q n m) := by
  induction n generalizing m with
  | zero => exact continuous_const
  | succ n ih =>
    apply continuous_finsetSum
    intro k _
    exact (continuous_const.mul (hq.continuous_iteratedDeriv k (WithTop.coe_le_coe.mpr (show (k:ℕ∞) ≤ ⊤ from le_top))).norm).mul (ih _)

 theorem angularTransportIterate_derivative_bound {q f : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 1 ≤ D) (n m : ℕ) (x : ℝ)
    (hb : ∀ k ≤ n+m, ‖iteratedDeriv k f x‖ ≤ C*D^k) :
    ‖iteratedDeriv m (angularTransportIterate q n f) x‖ ≤
      angularTransportCost q n m x * (C*D^(n+m)) := by
  induction n generalizing m with
  | zero => simpa [angularTransportIterate,angularTransportCost] using hb m (by omega)
  | succ n ih =>
    have hqn : ContDiffAt ℝ (m+1:ℕ) q x :=
      (hq.of_le (WithTop.coe_le_coe.mpr (show ((m+1:ℕ):ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    have hin : ContDiffAt ℝ (m+1:ℕ) (angularTransportIterate q n f) x :=
      ((angularTransportIterate_contDiff hq hf n).of_le (WithTop.coe_le_coe.mpr (show ((m+1:ℕ):ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    change ‖iteratedDeriv m (deriv (fun y => q y * angularTransportIterate q n f y)) x‖ ≤ _
    rw [← iteratedDeriv_succ',iteratedDeriv_fun_mul hqn hin]
    change ‖_‖ ≤ (∑ k ∈ Finset.range (m+2), _) * _
    rw [Finset.sum_mul]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k hk
    simp only [norm_mul,Complex.norm_natCast]
    have hl : n+(m+1-k) ≤ n+1+m := by omega
    have hh := ih (m+1-k) (fun j hj => hb j (hj.trans hl))
    have hp : C*D^(n+(m+1-k)) ≤ C*D^(n+1+m) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hl) hC
    calc
      _ ≤ ((m+1).choose k:ℝ) * ‖iteratedDeriv k q x‖ *
          (angularTransportCost q n (m+1-k) x * (C*D^(n+1+m))) := by
        gcongr
        exact hh.trans (mul_le_mul_of_nonneg_left hp (angularTransportCost_nonneg _ _ _ _))
      _ = _ := by ring

 theorem angularTransportIterate_uniform_bound {q : ℝ → ℂ} (hq : ContDiff ℝ ∞ q)
    {K : Set ℝ} (hK : IsCompact K) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
      ∀ {C D : ℝ}, 0 ≤ C → 1 ≤ D →
      (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
      ∀ x ∈ K, ‖angularTransportIterate q n f x‖ ≤ A*C*D^n := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (angularTransportCost_continuous hq n 0).continuousOn
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro f hf C D hC hD hb x hx
  have hh := angularTransportIterate_derivative_bound hq hf hC hD n 0 x (by simpa using fun k hk => hb k hk x)
  simp only [iteratedDeriv_zero,Nat.add_zero] at hh
  have hA : angularTransportCost q n 0 x ≤ max 0 B :=
    (le_abs_self _).trans ((hB x hx).trans (le_max_right _ _))
  apply hh.trans
  calc
    _ ≤ max 0 B * (C*D^n) := mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by ring

end PlanarFalconer

end OAI
