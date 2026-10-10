import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGapLong
import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGapNumerics

namespace OAI

noncomputable section
namespace Ostmann.Characters
open Filter
open scoped Topology BigOperators SchwartzMap

theorem eventually_oneSided_bilinear_scale_gap
    {τ : Type*} [Fintype τ] (C z : ℝ) (d : ℕ)
    {α β γ c : ℝ} (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α)
    (hαβ : α ≤ β) (hβγ : β < γ) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ L : ℝ in atTop,
    ∀ {η κ σ : Type} [Fintype η] [Fintype κ] [Fintype σ],
    ∀ (ρ : 𝓢(ℝ,ℂ)) (q : κ → ℕ), (∀ j, (q j).Prime) → Function.Injective q →
    ∀ (χ : ∀ j, MulChar (ZMod (q j)) ℂ), (∀ j, χ j ≠ 1) →
    ∀ (Q N : ℕ) (a : η → ℕ), (∀ j, Q.Coprime (q j)) →
    ∀ (μ : η × Fin N → ℝ) (ν : κ → ℝ)
      (U : η × Fin N → ℂ) (V : κ → ℂ) (W : η → ℕ → κ → ℂ)
      (E b₀ : ℝ), 0 ≤ E → 0 < b₀ →
    (N : ℝ) ≤ 3*b₀ →
    (∀ x, 0 ≤ μ x) → (∑ x, μ x ≤ 1) →
    (∀ x : η × Fin N, μ x ≤ longProgressionMajorant E b₀ Q (a x.1) x.2) →
    (∀ j, 0 ≤ ν j) → (∑ j, ν j ≤ 1) →
    (∀ x, ‖U x‖ ≤ 1) → (∀ j, ‖V j‖ ≤ 1) →
    ∀ (data : η → κ → κ → HistoryPolynomialData σ τ)
      (A B : τ → ℝ) (M : ℝ),
    (∀ r j k, j ≠ k → (data r j k).Ranges ρ A B M) →
    (∀ r j k, j ≠ k → ∀ n, n ≤ N →
      crossProgressionWeight (longProgressionMajorant E b₀ Q (a r)) (W r) j k n =
        (E/b₀ : ℂ)*(data r j k).weight ρ ((Q*n+a r : ℕ) : ℝ)) →
    Fintype.card η ≤ Q → (Q : ℝ) ≤ Real.exp (historyPolynomialCost C z d L) →
    E ≤ Real.exp (historyPolynomialCost C z d L) →
    (∀ r n j, ‖W r n j‖ ≤ Real.exp (historyPolynomialCost C z d L)) →
    (∀ r j k, j ≠ k → ((data r j k).degreeCost : ℝ) ≤ Real.exp (historyPolynomialCost C z d L)) →
    M ≤ Real.exp (historyPolynomialCost C z d L) →
    3 + (∑ i : τ, (B i - A i)) ≤ Real.exp (historyPolynomialCost C z d L) →
    priorMaxAtom ν ≤ Real.exp (-c*Real.exp (α*L)) →
    (∀ j, Real.log (q j : ℝ) ≤ Real.exp (β*L)) →
    Real.exp (γ*L) ≤ Real.log b₀ →
    ‖oneSidedMean μ ν U V (rowCharacterKernel q χ Q N a W)‖ ≤
      Real.exp (-δ*Real.exp (α*L)) := by
  obtain ⟨δ,hδ,hdecay⟩ := eventually_history_budget_decay C z d (Fintype.card τ)
    hz hC hα hαβ hβγ hc
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hdecay] with L hL
  intro η κ σ _ _ _ ρ q hq hinj χ hχ Q N a hQ μ ν U V W E b₀ hE hb hN
    hμ hmass hmajorant hν hνmass hU hV data A B M hdata heq hrows hQsize
    hEsize hW hdegree hM hwidth hatom hshort hlong
  apply hL _ (norm_nonneg _)
  have hprime (j : κ) : (q j : ℝ) ≤ Real.exp (Real.exp (β*L)) := by
    have hp : (0:ℝ) < q j := by exact_mod_cast (hq j).pos
    simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr (hshort j)
  have hfinite := oneSided_bilinear_long_profile_bound ρ q hq hinj χ hχ Q N a hQ
    μ ν U V W hE hb (Real.exp_pos _).le hN hμ hmass hmajorant hν hνmass hU hV hW
    data A B M (historyPolynomialCost C z d L) hdata heq (Real.exp_pos _).le hprime
    hdegree hM hwidth
  apply hfinite.trans
  apply longProfileBudget_le_exponentials (Fintype.card τ)
    (by unfold priorMaxAtom; positivity) (Nat.cast_nonneg _) hE hb (Real.exp_pos _).le
    (Real.exp_pos _).le hatom
  · exact (by exact_mod_cast hrows : (Fintype.card η : ℝ) ≤ Q).trans hQsize
  · exact hEsize
  · exact le_refl _
  · exact le_refl _
  · simpa only [Real.exp_log hb] using Real.exp_le_exp.mpr hlong

end Ostmann.Characters

end

end OAI
