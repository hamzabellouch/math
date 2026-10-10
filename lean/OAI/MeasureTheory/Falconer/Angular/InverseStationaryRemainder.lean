import OAI.MeasureTheory.Falconer.Angular.InverseStationaryCutoff

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff Topology

noncomputable def inverseDirectExpansion (q j : ℕ) (Λ : ℝ) (f : ℝ → ℂ) : ℂ :=
  Complex.exp (Complex.I*(Λ:ℂ)) * ((Λ^(-1/2:ℝ):ℝ):ℂ) *
    ∑ h ∈ Finset.range (q+1), ((Λ⁻¹:ℝ):ℂ)^h *
      directStationaryOperator h (inverseStationaryOperator j f) 0

theorem cutoff_inverse_expansion_eq (q j : ℕ) {Λ : ℝ} (hΛ : 0 < Λ)
    {ψ f : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hf : ContDiff ℝ ∞ f)
    (hψ₀ : ψ =ᶠ[𝓝 0] (fun _ => 1)) (hψπ : ψ =ᶠ[𝓝 Real.pi] (fun _ => 0)) :
    fullCircleStationaryExpansion Λ (fun y => ψ y*inverseStationaryOperator j f y) q =
      inverseDirectExpansion q j Λ f := by
  have hs := hψ.mul (inverseStationaryOperator_contDiff j hf)
  rw [fullCircleStationaryExpansion_one_sided hs (cutoff_inverse_opposite j hψπ),
    stationary_expansion_direct_operators hΛ hs]
  unfold inverseDirectExpansion
  rw [mul_assoc]
  congr 2
  apply Finset.sum_congr rfl
  intro h _
  rw [cutoff_inverse_jets j h hψ₀]

theorem cutoff_inverse_raw_remainder (q j M : ℕ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
    ∀ {ψ f : ℝ → ℂ}, ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ f →
    Function.Periodic ψ (2*Real.pi) → Function.Periodic f (2*Real.pi) →
    ψ =ᶠ[𝓝 0] (fun _ => 1) → ψ =ᶠ[𝓝 Real.pi] (fun _ => 0) →
    ∀ {P C D Λ : ℝ}, 0 ≤ P → 0 ≤ C → 1 ≤ D → 0 < Λ →
    (∀ k ≤ max (2*(q+1)+2) M, ∀ x, ‖iteratedDeriv k ψ x‖ ≤ P) →
    (∀ k ≤ max (2*(q+1)+2) M + 2*j, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖(∫ θ in (-Real.pi)..Real.pi,
        cosineOscillator Λ θ * (ψ θ * inverseStationaryOperator j f θ)) -
          inverseDirectExpansion q j Λ f‖ ≤
      Λ^(-1/2:ℝ)*A*P*C*D^(2*j+2)*(D^2/Λ)^(q+1) +
        B*P*C*D^(2*j+M)/Λ^M := by
  obtain ⟨A,B,hA,hB,hbound⟩ := full_circle_stationary_expansion q M
  let K := max (2*(q+1)+2) M
  let V : ℝ := 2^K*(inverseStationaryExpr j).cost
  have hV : 0 ≤ V := mul_nonneg (by positivity) (AngularDifferentialExpr.cost_nonneg _)
  refine ⟨Real.sqrt (2*Real.pi)*((2*Real.pi^2)^(q+1)/(q.factorial:ℝ))*A*V,
    B*V, by positivity, mul_nonneg hB hV, ?_⟩
  intro ψ f hψ hf hpψ hpf hψ₀ hψπ P C D Λ hP hC hD hΛ hbψ hbf
  have hs := hψ.mul (inverseStationaryOperator_contDiff j hf)
  have hp : Function.Periodic (fun y => ψ y*inverseStationaryOperator j f y) (2*Real.pi) :=
    hpψ.mul ((inverseStationaryExpr j).apply_periodic hpf)
  have hb := cutoff_inverse_derivative_bound j K hψ hf hP hC hD hbψ hbf
  have hCj : 0 ≤ 2^K*P*(inverseStationaryExpr j).cost*C*D^(2*j) := by
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hP)
        (AngularDifferentialExpr.cost_nonneg _)) hC
    · exact pow_nonneg (zero_le_one.trans hD) _
  have h := hbound hs hp hΛ hCj hD hb
  rw [cutoff_inverse_expansion_eq q j hΛ hψ hf hψ₀ hψπ] at h
  apply h.trans_eq
  rw [mul_assoc, stationary_remainder_factor, quadratic_scale_half hΛ]
  dsimp [V]
  simp only [pow_add]
  ring

end PlanarFalconer

end OAI
