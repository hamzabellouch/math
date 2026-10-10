import OAI.NumberTheory.Ostmann.Tree.RatioOrthogonality
import OAI.NumberTheory.Ostmann.Tree.TwoPairBare
import OAI.NumberTheory.Ostmann.Tree.TwoPairConvolution

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem twoPairConvolution_ratio_energy (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (L R : PairMode) (lam mu y : (ZMod p)ˣ) (hg0 : g 0=0) (hh0 : h 0=0) :
    (∑ ν : MulChar (ZMod p) ℂ,‖twoPairConvolution g h σ τ L R ν lam mu y‖^2) =
      (Fintype.card (ZMod p)ˣ:ℝ)*(p:ℝ)⁻¹^2*
        ∑ d : ZMod p,‖twoPairBare g h σ τ L R d (d-y) lam mu‖^2 := by
  let f : ZMod p → ℂ := fun d => twoPairBare g h σ τ L R d (d-y) lam mu
  have he (ν : MulChar (ZMod p) ℂ) :
      twoPairConvolution g h σ τ L R ν lam mu y =
      (p:ℂ)⁻¹*∑ d : ZMod p,f d*ν d*ν⁻¹ (d-y) := by
    unfold twoPairConvolution twoPairValue mean
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    dsimp [f,twoPairBare]
    ring
  have hfilter : (∑ d : ZMod p,if d=0 ∨ d=(y:ZMod p) then 0 else ‖f d‖^2)=∑ d : ZMod p,‖f d‖^2 := by
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d=0 ∨ d=(y:ZMod p)
    · rcases hd with hd | hd
      · subst d
        simp [f,twoPairBare_zero_left g h σ τ L R _ _ _ hg0]
      · subst d
        simp [f,twoPairBare_zero_right g h σ τ L R _ _ _ hh0]
    · simp [hd]
  simp_rw [he,norm_mul,norm_inv,Complex.norm_natCast,mul_pow]
  rw [← Finset.mul_sum,ratio_character_energy f y (Units.ne_zero y),hfilter]
  ring

def crossMajorant (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ) (L R : PairMode)
    (ν : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ :=
  (Fintype.card (ZMod p)ˣ:ℝ)⁻¹^2*
    ∑ lam : (ZMod p)ˣ,∑ mu : (ZMod p)ˣ,‖twoPairConvolution g h σ τ L R ν lam mu y‖^2

theorem crossMajorant_nonneg (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ) (L R : PairMode)
    (ν : MulChar (ZMod p) ℂ) (y : ZMod p) : 0≤crossMajorant g h σ τ L R ν y := by
  unfold crossMajorant
  positivity

theorem crossMajorant_sum (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ) (L R : PairMode)
    (y : (ZMod p)ˣ) (hg0 : g 0=0) (hh0 : h 0=0) :
    (∑ ν : MulChar (ZMod p) ℂ,crossMajorant g h σ τ L R ν y) =
      (Fintype.card (ZMod p)ˣ:ℝ)*(p:ℝ)⁻¹^2*
        ∑ d : ZMod p,pairSecondMoment g σ d*pairSecondMoment h τ (d-y) := by
  unfold crossMajorant
  rw [← Finset.mul_sum]
  have hs : (∑ ν : MulChar (ZMod p) ℂ,∑ lam : (ZMod p)ˣ,∑ mu : (ZMod p)ˣ,
      ‖twoPairConvolution g h σ τ L R ν lam mu y‖^2) =
      ∑ lam : (ZMod p)ˣ,∑ mu : (ZMod p)ˣ,∑ ν : MulChar (ZMod p) ℂ,
      ‖twoPairConvolution g h σ τ L R ν lam mu y‖^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro lam _
    rw [Finset.sum_comm]
  rw [hs]
  simp_rw [twoPairConvolution_ratio_energy g h σ τ L R _ _ y hg0 hh0]
  simp only [← Finset.mul_sum]
  rw [sum_three_rotate]
  calc
    _ = (Fintype.card (ZMod p)ˣ:ℝ)*(p:ℝ)⁻¹^2*
        ∑ d : ZMod p, (Fintype.card (ZMod p)ˣ:ℝ)⁻¹^2*
          ∑ lam : (ZMod p)ˣ,∑ mu : (ZMod p)ˣ,‖twoPairBare g h σ τ L R d (d-y) lam mu‖^2 := by
      rw [← Finset.mul_sum]
      ring
    _ = _ := by simp_rw [twoPairBare_parameter_average g h σ τ L R _ _ hg0 hh0]

end
end Ostmann.FiniteField

end OAI
