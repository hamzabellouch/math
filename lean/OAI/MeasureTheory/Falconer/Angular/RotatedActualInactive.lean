import OAI.MeasureTheory.Falconer.Geometry.InactiveBinDecay
import OAI.MeasureTheory.Falconer.Angular.ActualStationaryExpansion
import OAI.MeasureTheory.Falconer.Angular.CircleRotation

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem uniform_rotated_actual_inactive_bins {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) {a b : ℝ} (hab : a ≤ b) (hsw : tsupport w ⊆ Icc a b)
    {sig κ c T outer : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ) (hc : 0 < c)
    (K₁ K₂ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L : ℕ) (t u Λ : ℝ),
    κ*(N : ℝ) ≤ t → t ≤ u+2*sig*(N : ℝ) → 10*sig*(N : ℝ) ≤ u →
    (L : ℝ) ≤ u+2*sig*(N : ℝ) → c*(2 : ℝ)^(t+u) ≤ Λ →
    ∀ (e : UnitCircle) (φ axis : ℝ), |φ| ≤ Real.pi →
    dist (sourceUnitDirection φ) e ≤ graphUncappedAngularScale N sig t →
    (∀ θ ∈ tsupport w, 0 ≤ Real.cos (θ-φ)) →
    ∀ {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂],
    ∀ (S₁ : Finset ι₁) (b₁ : ι₁ → PolicyDescriptor) (k₁ : ι₁ → ℕ)
      (S₂ : Finset ι₂) (b₂ : ι₂ → PolicyDescriptor) (k₂ : ι₂ → ℕ),
    S₁.card ≤ (N+1)^3+1 → (∑ d ∈ S₁, k₁ d) ≤ K₁ →
    S₂.card ≤ (N+1)^3+1 → (∑ d ∈ S₂, k₂ d) ≤ K₂ →
    (∀ d ∈ S₁, descriptorLength (b₁ d) ≤ L) → (∀ d ∈ S₂, descriptorLength (b₂ d) ≤ L) →
    ∀ Q₁ Q₂ : DyadicSquare, 0 < Q₁.side → 0 < Q₂.side →
    ∀ (ρ₁ ρ₂ : Measure Plane) (m₁ m₂ : ℝ → ℝ) (lam₁ lam₂ : ℝ)
      (J₁ i₁ J₂ i₂ : ℕ) (h₁ h₂ : Plane → ℂ) (x y : Plane), ‖h₁ x‖ ≤ 1 → ‖h₂ y‖ ≤ 1 →
    let f := fun θ =>
      inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ h₁ x (sourceUnitDirection (θ+axis)) *
      conj (inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ h₂ y (sourceUnitDirection (θ+axis)))
    ((2 : ℝ)^N)^outer * ‖∫ θ : ℝ, cosineOscillator Λ (θ-φ) *
      (w θ * selectedBinAmplitude (graphUncappedAngularScale N sig t)
        (inactiveAngularLabels (angularBinCount (graphUncappedAngularScale N sig t)) e
          (3*graphUncappedAngularScale N sig t)) f θ)‖ ≤ ((2 : ℝ)^N)^(-T) := by
  obtain ⟨n,hn⟩ := inactive_bin_integral_power (T := T) (outer := outer) hw hab hsw hsig hgap hc
  obtain ⟨C₁,hC₁,N₁,h₁⟩ := uniform_actual_symbol_derivatives_upto hsig K₁ n
  obtain ⟨C₂,hC₂,N₂,h₂⟩ := uniform_actual_symbol_derivatives_upto hsig K₂ n
  obtain ⟨N₃,h₃⟩ := hn (C₁*C₂*2^n)
    (mul_nonneg (mul_nonneg hC₁ hC₂) (pow_nonneg zero_le_two n))
  refine ⟨max (max N₁ N₂) N₃,?_⟩
  intro N hN L t u Λ hlow ht hu hL hΛ e φ axis hφ hmove hcone ι₁ ι₂ inst₁ inst₂
    S₁ b₁ k₁ S₂ b₂ k₂ hc₁ hk₁ hc₂ hk₂ hl₁ hl₂ Q₁ Q₂ hQ₁ hQ₂
    ρ₁ ρ₂ m₁ m₂ lam₁ lam₂ J₁ i₁ J₂ i₂ hsp₁ hsp₂ x y hx hy
  let f₁ := fun θ => inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ hsp₁ x (sourceUnitDirection (θ+axis))
  let f₂ := fun θ => inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ hsp₂ y (sourceUnitDirection (θ+axis))
  have hf₁ : ContDiff ℝ ∞ f₁ :=
    (inheritedCircleSymbol_contDiff S₁ b₁ k₁ Q₁ hQ₁ ρ₁ m₁ N lam₁ sig J₁ i₁ hsp₁ x).comp
      (contDiff_id.add contDiff_const)
  have hf₂ : ContDiff ℝ ∞ f₂ :=
    (inheritedCircleSymbol_contDiff S₂ b₂ k₂ Q₂ hQ₂ ρ₂ m₂ N lam₂ sig J₂ i₂ hsp₂ y).comp
      (contDiff_id.add contDiff_const)
  have hb₁ := h₁ N ((le_max_left _ _).trans ((le_max_left _ _).trans hN))
    S₁ b₁ k₁ hc₁ hk₁ L hl₁ Q₁ hQ₁ ρ₁ m₁ lam₁ J₁ i₁ hsp₁ x hx
  have hb₂ := h₂ N ((le_max_right _ _).trans ((le_max_left _ _).trans hN))
    S₂ b₂ k₂ hc₂ hk₂ L hl₂ Q₂ hQ₂ ρ₂ m₂ lam₂ J₂ i₂ hsp₂ y hy
  have hs₁ (k : ℕ) (hk : k ≤ n) (θ : ℝ) :
      ‖iteratedDeriv k f₁ θ‖ ≤ C₁*(sourceSymbolScale N sig L)^k := by
    dsimp only [f₁]
    rw [iteratedDeriv_comp_add_const k
      (fun θ => inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ hsp₁ x (sourceUnitDirection θ))]
    exact hb₁ k hk (θ+axis)
  have hs₂ (k : ℕ) (hk : k ≤ n) (θ : ℝ) :
      ‖iteratedDeriv k f₂ θ‖ ≤ C₂*(sourceSymbolScale N sig L)^k := by
    dsimp only [f₂]
    rw [iteratedDeriv_comp_add_const k
      (fun θ => inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ hsp₂ y (sourceUnitDirection θ))]
    exact hb₂ k hk (θ+axis)
  apply h₃ N ((le_max_right _ _).trans hN) L t u Λ hlow ht hu hL hΛ e φ hφ hmove hcone
    (hf₁.mul (Complex.conjCLE.contDiff.comp hf₂))
  intro j hj θ
  have hbconj : ∀ k ≤ j, ‖iteratedDeriv k (fun z => conj (f₂ z)) θ‖ ≤ C₂*(sourceSymbolScale N sig L)^k := by
    intro k hk
    rw [complex_iteratedDeriv_conj hf₂, Complex.norm_conj]
    exact hs₂ k (hk.trans hj) θ
  have hh := complex_mul_derivative_scale hf₁ (Complex.conjCLE.contDiff.comp hf₂)
    hC₁ hC₂ (sourceSymbolScale_pos N sig L).le (sourceSymbolScale_pos N sig L).le j θ
    (fun k hk => hs₁ k (hk.trans hj) θ) hbconj
  apply hh.trans
  calc
    _ = (C₁*C₂*2^j)*(sourceSymbolScale N sig L)^j := by rw [← two_mul, mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_two hj) (mul_nonneg hC₁ hC₂)) (pow_nonneg (sourceSymbolScale_pos N sig L).le j)

end PlanarFalconer

end OAI
