import OAI.NumberTheory.Ostmann.Characters.HistoryArchimedeanVariationCost
import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGapMajorant

namespace OAI

noncomputable section
namespace Ostmann.Characters
open scoped BigOperators SchwartzMap

theorem oneSided_bilinear_long_profile_bound
    {η κ σ τ : Type*} [Fintype η] [Fintype κ] [Fintype σ] [Fintype τ]
    (ρ : 𝓢(ℝ,ℂ)) (q : κ → ℕ) (hq : ∀ j, (q j).Prime) (hinj : Function.Injective q)
    (χ : ∀ j, MulChar (ZMod (q j)) ℂ) (hχ : ∀ j, χ j ≠ 1)
    (Q N : ℕ) (a : η → ℕ) (hQ : ∀ j, Q.Coprime (q j))
    (μ : η × Fin N → ℝ) (ν : κ → ℝ)
    (U : η × Fin N → ℂ) (V : κ → ℂ) (W : η → ℕ → κ → ℂ)
    {E b₀ amplitude : ℝ} (hE : 0 ≤ E) (hb : 0 < b₀) (hamp : 0 ≤ amplitude)
    (hN : (N : ℝ) ≤ 3*b₀)
    (hμ : ∀ x, 0 ≤ μ x) (hmass : ∑ x, μ x ≤ 1)
    (hmajorant : ∀ x : η × Fin N, μ x ≤ longProgressionMajorant E b₀ Q (a x.1) x.2)
    (hν : ∀ j, 0 ≤ ν j) (hνmass : ∑ j, ν j ≤ 1)
    (hU : ∀ x, ‖U x‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1)
    (hW : ∀ r n j, ‖W r n j‖ ≤ amplitude)
    (data : η → κ → κ → HistoryPolynomialData σ τ)
    (A B : τ → ℝ) (M cost : ℝ)
    (hdata : ∀ r j k, j ≠ k → (data r j k).Ranges ρ A B M)
    (heq : ∀ r j k, j ≠ k → ∀ n, n ≤ N →
      crossProgressionWeight (longProgressionMajorant E b₀ Q (a r)) (W r) j k n =
        (E/b₀ : ℂ)*(data r j k).weight ρ ((Q*n+a r : ℕ) : ℝ))
    {P : ℝ} (hP : 0 ≤ P) (hprime : ∀ j, (q j : ℝ) ≤ P)
    (hdegree : ∀ r j k, j ≠ k → ((data r j k).degreeCost : ℝ) ≤ Real.exp cost)
    (hM : M ≤ Real.exp cost)
    (hwidth : 3 + (∑ i : τ, (B i - A i)) ≤ Real.exp cost) :
    ‖oneSidedMean μ ν U V (rowCharacterKernel q χ Q N a W)‖^2 ≤
      priorMaxAtom ν * (3*(Fintype.card η : ℝ)*E*amplitude^2) +
        (Fintype.card η : ℝ)*P^2*(E/b₀)*Real.exp (((Fintype.card τ : ℝ)+2)*cost) := by
  have h := oneSided_bilinear_profile_bound ρ q hq hinj χ hχ Q N a hQ μ
    (fun r => longProgressionMajorant E b₀ Q (a r)) ν U V W hμ hmass hmajorant
    hν hνmass hU hV data A B M (E/b₀ : ℂ) hdata heq hP (Real.exp_pos _).le hprime
    (fun r j k hjk => (data r j k).variationCost_le_exp ρ (hdata r j k hjk)
      (hdegree r j k hjk) hM hwidth)
  have hnorm : ‖(E/b₀ : ℂ)‖ = E/b₀ := by
    rw [← Complex.ofReal_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hE hb.le)]
  rw [hnorm] at h
  apply h.trans
  apply add_le_add _ le_rfl
  exact mul_le_mul_of_nonneg_left
    (longProgressionMajorant_energy_le Q N a ν W hE hb hamp hN hν hνmass hW)
    (by unfold priorMaxAtom; positivity)

end Ostmann.Characters

end

end OAI
