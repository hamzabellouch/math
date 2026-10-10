import OAI.MeasureTheory.Falconer.Angular.InverseStationaryRemainder
import OAI.MeasureTheory.Falconer.Angular.InverseStationaryScales

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff Topology

noncomputable def inverseStationaryWeight (Λ : ℝ) (j : ℕ) : ℝ :=
  Λ^(1/2:ℝ)*(Λ⁻¹)^j

theorem inverseStationaryWeight_nonneg {Λ : ℝ} (hΛ : 0 ≤ Λ) (j : ℕ) :
    0 ≤ inverseStationaryWeight Λ j := by
  unfold inverseStationaryWeight
  positivity

theorem cutoff_inverse_weighted_remainder (n j : ℕ) (hj : j ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧
    ∀ {ψ f : ℝ → ℂ}, ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ f →
    Function.Periodic ψ (2*Real.pi) → Function.Periodic f (2*Real.pi) →
    ψ =ᶠ[𝓝 0] (fun _ => 1) → ψ =ᶠ[𝓝 Real.pi] (fun _ => 0) →
    ∀ {P C D Λ : ℝ}, 0 ≤ P → 0 ≤ C → 1 ≤ D → 1 ≤ Λ → D^2/Λ ≤ 1 →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k ψ x‖ ≤ P) →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖(inverseStationaryWeight Λ j:ℂ) *
      ((∫ θ in (-Real.pi)..Real.pi,
        cosineOscillator Λ θ * (ψ θ * inverseStationaryOperator j f θ)) -
          inverseDirectExpansion (n-j) j Λ f)‖ ≤
        A*P*C*D^2*(D^2/Λ)^(n+1) := by
  obtain ⟨A,B,hA,hB,hh⟩ := cutoff_inverse_raw_remainder (n-j) j (2*(n+1))
  refine ⟨A+B, add_nonneg hA hB, ?_⟩
  intro ψ f hψ hf hpψ hpf hψ₀ hψπ P C D Λ hP hC hD hΛ hr hbψ hbf
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hk : max (2*(n-j+1)+2) (2*(n+1)) + 2*j ≤ 4*(n+1)+2 := by omega
  have h := hh hψ hf hpψ hpf hψ₀ hψπ hP hC hD hΛp
    (fun k hk' => hbψ k (by omega)) (fun k hk' => hbf k (hk'.trans hk))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inverseStationaryWeight_nonneg hΛp.le j)]
  apply (mul_le_mul_of_nonneg_left h (inverseStationaryWeight_nonneg hΛp.le j)).trans
  rw [mul_add]
  change (Λ^(1/2:ℝ)*(Λ⁻¹)^j) * _ + (Λ^(1/2:ℝ)*(Λ⁻¹)^j) * _ ≤ _
  rw [inverse_local_remainder_factor _ _ hΛp]
  have he : n-j+1+j = n+1 := by omega
  rw [he]
  have hn := inverse_nonstationary_remainder_bound j (n+1) (by omega)
    hΛ hB hP hC hD hr
  calc
    _ ≤ A*P*C*D^2*(D^2/Λ)^(n+1) + B*P*C*D^2*(D^2/Λ)^(n+1) :=
      add_le_add (le_refl _) hn
    _ = _ := by ring

end PlanarFalconer

end OAI
