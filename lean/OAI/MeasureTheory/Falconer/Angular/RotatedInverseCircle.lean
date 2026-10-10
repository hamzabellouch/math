import OAI.MeasureTheory.Falconer.Angular.InverseCirclePower
import OAI.MeasureTheory.Falconer.Angular.RotatedCircleIntegral

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff Topology

noncomputable def rotatedInverseCircleIntegral (n : ℕ) (Λ θ₀ : ℝ)
    (ψ f : ℝ → ℂ) : ℂ :=
  ((Λ^(1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1), ((Λ⁻¹:ℝ):ℂ)^j *
    ∫ θ in (-Real.pi)..Real.pi,
      cosineOscillator Λ (θ-θ₀) * (ψ θ * inverseStationaryOperator j f θ)

theorem rotatedInverseCircleIntegral_eq (n : ℕ) (Λ θ₀ : ℝ) {ψ f : ℝ → ℂ}
    (hpψ : Function.Periodic ψ (2*Real.pi)) (hpf : Function.Periodic f (2*Real.pi)) :
    rotatedInverseCircleIntegral n Λ θ₀ ψ f =
      inverseCircleIntegral n Λ (fun θ => ψ (θ+θ₀)) (fun θ => f (θ+θ₀)) := by
  unfold rotatedInverseCircleIntegral inverseCircleIntegral
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hp : Function.Periodic (fun θ => ψ θ * inverseStationaryOperator j f θ) (2*Real.pi) :=
    hpψ.mul ((inverseStationaryExpr j).apply_periodic hpf)
  rw [rotated_circle_integral Λ θ₀ hp]
  simp only [inverseStationaryOperator, AngularDifferentialExpr.apply_shift]

theorem shifted_periodic {f : ℝ → ℂ} {a : ℝ} (hf : Function.Periodic f a) (b : ℝ) :
    Function.Periodic (fun x => f (x+b)) a := by
  intro x
  change f (x+a+b) = f (x+b)
  rw [show x+a+b = (x+b)+a by ring, hf]

theorem shifted_germ {f g : ℝ → ℂ} {a b : ℝ} (h : f =ᶠ[𝓝 (a+b)] g) :
    (fun x => f (x+b)) =ᶠ[𝓝 a] (fun x => g (x+b)) := by
  exact h.comp_tendsto
    ((show Continuous (fun x : ℝ => x+b) from continuous_id.add continuous_const).continuousAt)

theorem rotated_inverse_circle_power {c sig T : ℝ} (hc : 0 < c) (hsig : 0 < sig) :
    ∃ n : ℕ, ∀ P C : ℝ, 0 ≤ P → 0 ≤ C → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ψ f : ℝ → ℂ}, ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ f →
    Function.Periodic ψ (2*Real.pi) → Function.Periodic f (2*Real.pi) →
    ∀ θ₀ : ℝ, ψ =ᶠ[𝓝 θ₀] (fun _ => 1) → ψ =ᶠ[𝓝 (θ₀+Real.pi)] (fun _ => 0) →
    ∀ {D Λ : ℝ}, 1 ≤ D → ((2:ℝ)^N)^(c*sig) ≤ Λ →
    D ≤ ((2:ℝ)^N)^(1+sig) → D^2/Λ ≤ ((2:ℝ)^N)^(-c*sig) →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k ψ x‖ ≤ P) →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖Complex.exp (Complex.I*(Λ:ℂ))*f θ₀ - rotatedInverseCircleIntegral n Λ θ₀ ψ f‖ ≤
      ((2:ℝ)^N)^(-T) := by
  obtain ⟨n,hn⟩ := inverse_circle_stationary_power (T := T) hc hsig
  refine ⟨n, ?_⟩
  intro P C hP hC
  obtain ⟨N₀,hN₀⟩ := hn P C hP hC
  refine ⟨N₀, ?_⟩
  intro N hN ψ f hψ hf hpψ hpf θ₀ hψ₀ hψπ D Λ hD hlower hupper hratio hbψ hbf
  have hzero : (fun θ => ψ (θ+θ₀)) =ᶠ[𝓝 0] (fun _ => 1) :=
    shifted_germ (a := 0) (b := θ₀) (f := ψ) (g := fun _ => 1) (by simpa using hψ₀)
  have hpi : (fun θ => ψ (θ+θ₀)) =ᶠ[𝓝 Real.pi] (fun _ => 0) :=
    shifted_germ (a := Real.pi) (b := θ₀) (f := ψ) (g := fun _ => 0)
      (by simpa only [add_comm] using hψπ)
  rw [rotatedInverseCircleIntegral_eq n Λ θ₀ hpψ hpf]
  simpa only [zero_add] using hN₀ N hN
    (ψ := fun θ => ψ (θ+θ₀)) (f := fun θ => f (θ+θ₀))
    (hψ.comp (contDiff_id.add contDiff_const)) (hf.comp (contDiff_id.add contDiff_const))
    (shifted_periodic hpψ θ₀) (shifted_periodic hpf θ₀) hzero hpi
    hD hlower hupper hratio
    (fun k hk x => by rw [iteratedDeriv_comp_add_const]; exact hbψ k hk _)
    (fun k hk x => by rw [iteratedDeriv_comp_add_const]; exact hbf k hk _)

end PlanarFalconer

end OAI
