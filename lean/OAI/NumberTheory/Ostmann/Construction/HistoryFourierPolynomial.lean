import OAI.NumberTheory.Ostmann.Construction.HistoryPolynomialSpecialization
import OAI.NumberTheory.Ostmann.Characters.NormalizedFourierProfile

namespace OAI

/-! # Fourier weights of reconstructed histories in the long prime variable -/

namespace Ostmann

open scoped SchwartzMap Classical

noncomputable def historyFourierFactor {σ : Type*} (P : MvPolynomial σ ℤ)
    (a : σ → ℝ) (i : σ) (d X : ℝ) (ψ : 𝓢(ℝ, ℂ))
    (v lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) : ClippedPolynomialFactor :=
  fourierPolynomialFactor (normalizedHistoryPolynomial P a i (d * X)) ψ v lo hi hlo hhi

/-- This is the actual level-zero Fourier weight after fixing the other
variables and substituting the cleared history numerator. -/
theorem historyFourierFactor_value {σ : Type*} (P : MvPolynomial σ ℤ)
    (a : σ → ℝ) (i : σ) (d X : ℝ) (ψ : 𝓢(ℝ, ℂ))
    (v lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (x : ℝ)
    (hd : d ≠ 0) (hX : X ≠ 0)
    (hP : MvPolynomial.eval₂ (Int.castRingHom ℝ) (Function.update a i x) P ≠ 0)
    (hrange : (MvPolynomial.eval₂ (Int.castRingHom ℝ) (Function.update a i x) P / d) / X ∈
      Set.Icc lo hi) :
    (historyFourierFactor P a i d X ψ v lo hi hlo hhi).value x =
      archimedeanLeafFactor X
        (MvPolynomial.eval₂ (Int.castRingHom ℝ) (Function.update a i x) P / d) v 1 ψ := by
  have he : (normalizedHistoryPolynomial P a i (d * X)).eval x =
      (MvPolynomial.eval₂ (Int.castRingHom ℝ) (Function.update a i x) P / d) / X := by
    rw [normalizedHistoryPolynomial_eval, div_div]
  exact fourierPolynomialFactor_original _ ψ v lo hi hlo hhi x X _ hX
    (div_ne_zero hP hd) he (he.symm ▸ hrange)

theorem historyFourierFactor_degree {σ : Type*} (P : MvPolynomial σ ℤ)
    (a : σ → ℝ) (i : σ) (d X : ℝ) (ψ : 𝓢(ℝ, ℂ))
    (v lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) :
    (historyFourierFactor P a i d X ψ v lo hi hlo hhi).polynomial.derivative.natDegree ≤
      P.totalDegree := by
  apply (Polynomial.natDegree_derivative_le _).trans
  exact (Nat.sub_le _ _).trans (normalizedHistoryPolynomial_natDegree P a i (d * X))

theorem historyFourierFactor_budget {σ : Type*} (P : MvPolynomial σ ℤ)
    (a : σ → ℝ) (i : σ) (d X : ℝ) (ψ : 𝓢(ℝ, ℂ))
    (v lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) :
    2 * (historyFourierFactor P a i d X ψ v lo hi hlo hhi).bound +
      (historyFourierFactor P a i d X ψ v lo hi hlo hhi).lip *
        ((historyFourierFactor P a i d X ψ v lo hi hlo hhi).hi -
          (historyFourierFactor P a i d X ψ v lo hi hlo hhi).lo) =
      2 * SchwartzMap.seminorm ℝ 0 0 ψ +
        (SchwartzMap.seminorm ℝ 0 0 ψ + SchwartzMap.seminorm ℝ 0 1 ψ * |v|) * (hi - lo) := rfl

end Ostmann

end OAI
