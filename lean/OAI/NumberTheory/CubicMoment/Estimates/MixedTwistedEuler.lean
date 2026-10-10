import OAI.NumberTheory.CubicMoment.Estimates.MixedPrimitiveData
import OAI.NumberTheory.CubicMoment.Estimates.RamifiedIdealParts

namespace OAI

/-! Exact ramified Euler restoration for the norm-twisted primary mixed
sum. These are the sums to which the smooth primitive bound is applied. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primary_mixed_twisted_euler {a b d : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (ψ : MulChar (Residues d) ℂ)
    (hu : ∀ v : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) v) = 1)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) (t : ℝ) :
    (∑' x : Eisenstein, if primary x then
      mixedCubic a b x*mellinPhase t (norm x)*W (norm x/Z) else 0) =
      ∑ T ∈ ramifiedIdealPrimes.powerset,
        (-1:ℂ)^T.card*residueIdealChar d ψ (primeSetExponent T)*
          mellinPhase t (idealExponentNorm (primeSetExponent T))*
          ∑' ν, residueIdealChar d ψ ν*mellinPhase t (idealExponentNorm ν)*
            W (idealExponentNorm ν/(Z/idealExponentNorm (primeSetExponent T))) := by
  let χ (ν : EisensteinIdealExponent) :=
    residueIdealChar d ψ ν*mellinPhase t (idealExponentNorm ν)
  have hχ (ν κ : EisensteinIdealExponent) : χ (ν+κ) = χ ν*χ κ := by
    dsimp only [χ]
    rw [residueIdealChar_add,idealExponentNorm_add,
      mellinPhase_mul_pos t (idealExponentNorm_pos ν) (idealExponentNorm_pos κ)]
    ring
  have hm (x : Eisenstein) (hx : primary x) :
      residueIdealChar d ψ (idealExponentOf x) = mixedCubic a b x := by
    rw [primitive_ideal_mixed_match ha hb hsa hsb hab ψ hu hagree
      (idealExponentOf x)]
    · exact primaryMixedIdealChar_at_element ha hb hx
    · simpa only [idealPrimaryGenerator_at_element hx] using hx
  calc
    _ = ∑' x : Eisenstein, if primary x then
        χ (idealExponentOf x)*W (norm x/Z) else 0 := by
      apply tsum_congr
      intro x
      by_cases hx : primary x
      · rw [ite_eq_left hx,ite_eq_left hx]
        dsimp only [χ]
        rw [hm x hx,idealExponentOf_norm (primary_ne_zero hx)]
      · rw [ite_eq_right hx,ite_eq_right hx]
    _ = _ := by simpa only [χ,mul_assoc] using primary_element_smooth_euler χ hχ W hW hZ

end CubicFirstMoment

end

end OAI
