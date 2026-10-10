import OAI.MeasureTheory.Falconer.Angular.ActualFullCircleStationary
import OAI.MeasureTheory.Falconer.Geometry.SelectedBinAmplitude

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

 theorem complex_pair_derivatives_upto {f g : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {C B D : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hD : 0 ≤ D) (n : ℕ)
    (hbf : ∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k)
    (hbg : ∀ k ≤ n, ∀ x, ‖iteratedDeriv k g x‖ ≤ B*D^k) :
    ∀ j ≤ n, ∀ x, ‖iteratedDeriv j (fun y => f y*conj (g y)) x‖ ≤
      (C*B*2^n)*D^j := by
  intro j hj x
  have hbc : ∀ k ≤ j, ‖iteratedDeriv k (fun y => conj (g y)) x‖ ≤ B*D^k := by
    intro k hk
    rw [complex_iteratedDeriv_conj hg,Complex.norm_conj]
    exact hbg k (hk.trans hj) x
  apply (complex_mul_derivative_scale hf (Complex.conjCLE.contDiff.comp hg)
    hC hB hD hD j x (fun k hk => hbf k (hk.trans hj) x) hbc).trans
  calc
    _ = (C*B*2^j)*D^j := by rw [← two_mul,mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) (mul_nonneg hC hB))
      (pow_nonneg hD j)

 theorem uniform_actual_two_point_stationary {c sig T : ℝ}
    (hc : 0 < c) (hsig : 0 < sig) (K : ℕ) :
    ∃ n N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    S.card ≤ (N+1)^3+1 → (∑ a ∈ S, k a) ≤ K →
    ∀ L ≤ N, (∀ a ∈ S, descriptorLength (b a) ≤ L) →
    ∀ Q : DyadicSquare, 0 < Q.side → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (h : Plane → ℂ) (x y : Plane),
    ‖h x‖ ≤ 1 → ‖h y‖ ≤ 1 →
    ∀ θ₀ Λ : ℝ, ((2:ℝ)^N)^(c*sig) ≤ Λ →
    sourceSymbolScale N sig L^2/Λ ≤ ((2:ℝ)^N)^(-c*sig) →
    let f := fun φ =>
      inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection φ) *
      conj (inheritedCircleSymbol S b k Q ρ m N lam sig J i h y (sourceUnitDirection φ))
    ‖(∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ (θ-θ₀)*f θ) -
      fullCircleStationaryExpansion Λ (fun θ => f (θ+θ₀)) n‖ ≤
      Λ^(-1/2:ℝ)*((2:ℝ)^N)^(-T) := by
  obtain ⟨n,hn⟩ := full_circle_stationary_power (T := T) hc hsig
  let q := 2*(n+1)+2
  obtain ⟨C,hC,N₁,h₁⟩ := uniform_actual_symbol_derivatives_upto hsig K q
  obtain ⟨N₂,h₂⟩ := hn (C*C*2^q) (by positivity)
  refine ⟨n,max N₁ N₂,?_⟩
  intro N hN ι inst S b k hcard hK L hLN hL Q hQ ρ m lam J i h x y hx hy θ₀ Λ hlower hratio
  let fx := fun φ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection φ)
  let fy := fun φ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h y (sourceUnitDirection φ)
  let f := fun φ => fx φ*conj (fy φ)
  have hfx : ContDiff ℝ ∞ fx := inheritedCircleSymbol_contDiff S b k Q hQ ρ m N lam sig J i h x
  have hfy : ContDiff ℝ ∞ fy := inheritedCircleSymbol_contDiff S b k Q hQ ρ m N lam sig J i h y
  have hf : ContDiff ℝ ∞ f := hfx.mul (Complex.conjCLE.contDiff.comp hfy)
  have hp : Function.Periodic f (2*Real.pi) := by
    intro θ
    have hpx : Function.Periodic fx (2*Real.pi) :=
      inheritedCircleSymbol_periodic S b k Q ρ m N lam sig J i h x
    have hpy : Function.Periodic fy (2*Real.pi) :=
      inheritedCircleSymbol_periodic S b k Q ρ m N lam sig J i h y
    change fx (θ+2*Real.pi)*conj (fy (θ+2*Real.pi)) = fx θ*conj (fy θ)
    rw [hpx,hpy]
  have hb := complex_pair_derivatives_upto hfx hfy hC hC (sourceSymbolScale_pos N sig L).le q
    (h₁ N ((le_max_left _ _).trans hN) S b k hcard hK L hL Q hQ ρ m lam J i h x hx)
    (h₁ N ((le_max_left _ _).trans hN) S b k hcard hK L hL Q hQ ρ m lam J i h y hy)
  have hfs : ContDiff ℝ ∞ (fun θ => f (θ+θ₀)) := hf.comp (contDiff_id.add contDiff_const)
  have hps : Function.Periodic (fun θ => f (θ+θ₀)) (2*Real.pi) := by
    intro θ
    change f (θ+2*Real.pi+θ₀) = f (θ+θ₀)
    rw [show θ+2*Real.pi+θ₀ = (θ+θ₀)+2*Real.pi by ring,hp]
  change ‖(∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ (θ-θ₀)*f θ) - _‖ ≤ _
  rw [rotated_circle_integral Λ θ₀ hp]
  apply h₂ N ((le_max_right _ _).trans hN) hfs hps (sourceSymbolScale_one_le N hsig.le L)
    hlower (sourceSymbolScale_upper N hsig.le hLN) hratio
  intro j hj θ
  rw [iteratedDeriv_comp_add_const]
  exact hb j hj _

end PlanarFalconer

end OAI
