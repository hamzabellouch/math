import OAI.NumberTheory.CubicMoment.Estimates.PrimaryCharacterNonprincipal
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryIdealMoments
import OAI.NumberTheory.CubicMoment.Estimates.ResidueIdealCharacters
import OAI.NumberTheory.CubicMoment.Estimates.ConductorLocal

namespace OAI

/-! Exact arithmetic reduction of the original primary mixed-character
sum to complete primitive ideal sums. Every Euler rescaling is retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_mixed_smooth_eq_ideal {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) :
    (∑' x : Eisenstein, if primary x then mixedCubic a b x*W (norm x/Z) else 0) =
      ∑' ν, residueIdealChar (3*(a*b)) (primaryMixedResidueChar a b ha hb) ν*
        W (idealExponentNorm ν/Z) := by
  calc
    _ = ∑' x : Eisenstein, if primary x then
        primaryMixedIdealChar a b (idealExponentOf x)*W (norm x/Z) else 0 := by
      apply tsum_congr
      intro x
      by_cases hx : primary x
      · rw [ite_eq_left hx,ite_eq_left hx,primaryMixedIdealChar_at_element ha hb hx]
      · rw [ite_eq_right hx,ite_eq_right hx]
    _ = ∑' ν, if primary (idealPrimaryGenerator ν) then
        primaryMixedIdealChar a b ν*W (idealExponentNorm ν/Z) else 0 :=
      primary_element_ideal_smooth_eq (primaryMixedIdealChar a b) W hW hZ
    _ = _ := by
      apply tsum_congr
      intro ν
      rw [residueIdealChar_primaryMixed ha hb]
      by_cases hν : primary (idealPrimaryGenerator ν)
      · rw [ite_eq_left hν]
      · rw [ite_eq_right hν,primaryMixedIdealChar_eq,ite_eq_right hν,zero_mul]

/-- No primitive-character or character-agreement assumption remains in
this exact reduction. Primitivity, nonprincipality, unit-invariance and
the conductor upper bound are all supplied by the arithmetic proofs. -/
theorem primary_mixed_smooth_primitive_reduction {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hnu : ¬ IsUnit (a*b))
    (W : ℝ → ℂ) (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) :
    ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      d ≠ 0 ∧ PrimitiveResidueCharacter d ψ ∧ ψ ≠ 1 ∧
      normNat d ≤ normNat (3*(a*b)) ∧
      (∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1) ∧
      (∑' x : Eisenstein, if primary x then mixedCubic a b x*W (norm x/Z) else 0) =
        ∑ T ∈ (idealExponentOf (3*(a*b))).support.powerset,
          (-1:ℂ)^T.card*residueIdealChar d ψ (primeSetExponent T)*
            ∑' κ, residueIdealChar d ψ κ*
              W (idealExponentNorm κ/(Z/idealExponentNorm (primeSetExponent T))) := by
  obtain ⟨d,ψ,hd,hprim,hn,hN,hu,hind,_⟩ := mixed_primitive_conductor ha hb hsa hsb hab hnu
  refine ⟨d,ψ,hd,hprim,hn,hN,hu,?_⟩
  rw [primary_mixed_smooth_eq_ideal ha hb W hW hZ]
  exact induced_residue_smooth_euler
    (mul_ne_zero (by norm_num) (mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb))) hind W hW hZ

/-- The local conductor calculation reduces the Euler correction to the
fixed primes above three, independently of the varying squarefree modulus. -/
theorem primary_mixed_smooth_ramified_euler {a b d : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (ψ : MulChar (Residues d) ℂ)
    (hu : ∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) :
    (∑' x : Eisenstein, if primary x then mixedCubic a b x*W (norm x/Z) else 0) =
      ∑ T ∈ ramifiedIdealPrimes.powerset, (-1:ℂ)^T.card*
        residueIdealChar d ψ (primeSetExponent T)*
          ∑' κ, residueIdealChar d ψ κ*
            W (idealExponentNorm κ/(Z/idealExponentNorm (primeSetExponent T))) := by
  calc
    _ = ∑' x : Eisenstein, if primary x then
        primaryMixedIdealChar a b (idealExponentOf x)*W (norm x/Z) else 0 := by
      apply tsum_congr
      intro x
      by_cases hx : primary x
      · rw [ite_eq_left hx,ite_eq_left hx,primaryMixedIdealChar_at_element ha hb hx]
      · rw [ite_eq_right hx,ite_eq_right hx]
    _ = ∑' ν, if primary (idealPrimaryGenerator ν) then
        primaryMixedIdealChar a b ν*W (idealExponentNorm ν/Z) else 0 :=
      primary_element_ideal_smooth_eq (primaryMixedIdealChar a b) W hW hZ
    _ = ∑' ν, if primary (idealPrimaryGenerator ν) then
        residueIdealChar d ψ ν*W (idealExponentNorm ν/Z) else 0 := by
      apply tsum_congr
      intro ν
      by_cases hν : primary (idealPrimaryGenerator ν)
      · rw [ite_eq_left hν,ite_eq_left hν,
          primitive_ideal_mixed_match ha hb hsa hsb hab ψ hu hagree ν hν]
      · rw [ite_eq_right hν,ite_eq_right hν]
    _ = _ := primary_ideal_smooth_euler _ (residueIdealChar_add d ψ) W hW hZ

theorem primary_mixed_smooth_primitive_ramified {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hnu : ¬ IsUnit (a*b))
    (W : ℝ → ℂ) (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) :
    ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      d ≠ 0 ∧ PrimitiveResidueCharacter d ψ ∧ ψ ≠ 1 ∧
      normNat d ≤ normNat (3*(a*b)) ∧ a*b ∣ d ∧
      (∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1) ∧
      (∑' x : Eisenstein, if primary x then mixedCubic a b x*W (norm x/Z) else 0) =
        ∑ T ∈ ramifiedIdealPrimes.powerset, (-1:ℂ)^T.card*
          residueIdealChar d ψ (primeSetExponent T)*
            ∑' κ, residueIdealChar d ψ κ*
              W (idealExponentNorm κ/(Z/idealExponentNorm (primeSetExponent T))) := by
  obtain ⟨d,ψ,hd,hprim,hn,hN,hu,_,hagree⟩ := mixed_primitive_conductor ha hb hsa hsb hab hnu
  exact ⟨d,ψ,hd,hprim,hn,hN,mixed_conductor_contains ha hb hsa hsb hab ψ hagree,hu,
    primary_mixed_smooth_ramified_euler ha hb hsa hsb hab ψ hu hagree W hW hZ⟩

end CubicFirstMoment

end

end OAI
