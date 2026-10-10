import OAI.MeasureTheory.Falconer.Angular.InverseStationaryOperators
import OAI.MeasureTheory.Falconer.Angular.StationaryJetLocality

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

theorem AngularDifferentialExpr.apply_shift (p : AngularDifferentialExpr)
    (f : ℝ → ℂ) (a : ℝ) :
    p.apply (fun x => f (x+a)) = fun x => p.apply f (x+a) := by
  induction p generalizing f with
  | term c k => simp [apply, iteratedDeriv_comp_add_const]
  | add p q hp hq => simp [apply, hp, hq]
  | comp p q hp hq => simp only [apply, hq, hp]

theorem AngularDifferentialExpr.apply_periodic (p : AngularDifferentialExpr)
    {f : ℝ → ℂ} {a : ℝ} (hf : Function.Periodic f a) :
    Function.Periodic (p.apply f) a := by
  have he : (fun x => f (x+a)) = f := funext hf
  have h := p.apply_shift f a
  rw [he] at h
  intro x
  exact (congrFun h x).symm

theorem complex_product_derivative_bound {f g : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {A B D : ℝ}
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hD : 0 ≤ D) (m : ℕ) (x : ℝ)
    (hfb : ∀ k ≤ m, ‖iteratedDeriv k f x‖ ≤ A*D^k)
    (hgb : ∀ k ≤ m, ‖iteratedDeriv k g x‖ ≤ B*D^k) :
    ‖iteratedDeriv m (fun y => f y*g y) x‖ ≤ 2^m*A*B*D^m := by
  rw [iteratedDeriv_fun_mul (AngularDifferentialExpr.smooth_finite hf m x)
    (AngularDifferentialExpr.smooth_finite hg m x)]
  calc
    _ ≤ ∑ k ∈ Finset.range (m+1), (m.choose k:ℝ)*(A*D^k)*(B*D^(m-k)) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≤ m := by have := Finset.mem_range.mp hk; omega
      simp only [norm_mul, Complex.norm_natCast]
      gcongr
      · exact hfb k hk'
      · exact hgb (m-k) (Nat.sub_le _ _)
    _ = A*B*(D+D)^m := by
      rw [add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [← two_mul, mul_pow]; ring

theorem cutoff_inverse_derivative_bound (j K : ℕ) {ψ f : ℝ → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hf : ContDiff ℝ ∞ f) {P C D : ℝ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hbψ : ∀ k ≤ K, ∀ x, ‖iteratedDeriv k ψ x‖ ≤ P)
    (hbf : ∀ k ≤ K+2*j, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) :
    ∀ m ≤ K, ∀ x, ‖iteratedDeriv m
      (fun y => ψ y * inverseStationaryOperator j f y) x‖ ≤
        (2^K*P*(inverseStationaryExpr j).cost*C*D^(2*j))*D^m := by
  intro m hm x
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hCj : 0 ≤ (inverseStationaryExpr j).cost*C*D^(2*j) :=
    mul_nonneg (mul_nonneg (AngularDifferentialExpr.cost_nonneg _) hC) (pow_nonneg hD0 _)
  have h := complex_product_derivative_bound hψ (inverseStationaryOperator_contDiff j hf)
    hP hCj hD0 m x
    (fun k hk => (hbψ k (hk.trans hm) x).trans (by
      simpa using mul_le_mul_of_nonneg_left (one_le_pow₀ hD : 1 ≤ D^k) hP))
    (fun k hk => (inverseStationaryOperator_derivative_bound j k hf hC hD x
      (fun l hl => hbf l (by omega) x)).trans_eq (by rw [pow_add]; ring))
  apply h.trans
  calc
    _ ≤ 2^K*P*((inverseStationaryExpr j).cost*C*D^(2*j))*D^m := by
      gcongr
      norm_num
    _ = _ := by ring

theorem cutoff_inverse_jets (j h : ℕ) {ψ f : ℝ → ℂ} {x : ℝ}
    (hψ : ψ =ᶠ[𝓝 x] (fun _ => 1)) :
    directStationaryOperator h (fun y => ψ y*inverseStationaryOperator j f y) x =
      directStationaryOperator h (inverseStationaryOperator j f) x := by
  apply directStationaryOperator_congr
  filter_upwards [hψ] with y hy
  simp [hy]

theorem cutoff_inverse_opposite (j : ℕ) {ψ f : ℝ → ℂ}
    (hψ : ψ =ᶠ[𝓝 Real.pi] (fun _ => 0)) :
    (fun y => ψ y*inverseStationaryOperator j f y) =ᶠ[𝓝 Real.pi] (fun _ => 0) := by
  filter_upwards [hψ] with y hy
  simp [hy]

end PlanarFalconer

end OAI
