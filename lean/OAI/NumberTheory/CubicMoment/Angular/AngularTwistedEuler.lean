import OAI.NumberTheory.CubicMoment.Angular.AngularTwistedIdealMatch

namespace OAI

/-! Exact Euler restoration for the small-twisted primary sum. Only the
primes above three and the fixed small modulus are omitted, with the
angular character and its unit compatibility retained exactly. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma angular_twisted_residue_restriction {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hr : r ≠ 0) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (ℓ : ℤ) (hu : AngularUnitCompatible d ψ ℓ)
    (hη : AngularUnitCompatible r η ℓ)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x))
    (ν : EisensteinIdealExponent) :
    primaryMixedIdealChar a b ν*angularResidueIdealChar r η ℓ ν =
      if ∀ p ∈ (idealExponentOf (3*r)).support, ν p = 0 then angularResidueIdealChar d ψ ℓ ν else 0 := by
  have h3r : (3:Eisenstein)*r ≠ 0 := mul_ne_zero (by norm_num) hr
  by_cases hlocal : ∀ p ∈ (idealExponentOf (3*r)).support, ν p = 0
  · rw [ite_eq_left hlocal]
    have hcop := (ideal_coprime_support h3r ν).mpr hlocal
    have hprim : primary (idealPrimaryGenerator ν) :=
      (idealPrimaryGenerator_primary_iff ν).mpr
        ((idealGenerator_coprime_three_iff ν).mp hcop.of_mul_left_left.symm)
    have hpr : IsCoprime r (idealPrimaryGenerator ν) :=
      hcop.of_mul_left_right.of_isCoprime_of_dvd_right
        (primaryNormalize_associated (idealExponentGenerator ν)).symm.dvd
    exact (angular_twisted_ideal_mixed_match ha hb hsa hsb hab hsmall ψ η ℓ hu hη hagree ν hprim hpr).symm
  · rw [ite_eq_right hlocal]
    by_cases hprim : primary (idealPrimaryGenerator ν)
    · have hn : ¬ IsCoprime r (idealExponentGenerator ν) := by
        intro hc
        apply hlocal
        apply (ideal_coprime_support h3r ν).mp
        exact ((idealGenerator_coprime_three_iff ν).mpr
          ((idealPrimaryGenerator_primary_iff ν).mp hprim)).symm.mul_left hc
      have hz : angularResidueIdealChar r η ℓ ν = 0 := by
        have hzero : residueIdealChar r η ν = 0 :=
          MulChar.map_nonunit η (fun h => hn (isCoprime_of_residue_isUnit h))
        rw [angularResidueIdealChar,hzero,zero_mul]
      rw [hz,mul_zero]
    · rw [primaryMixedIdealChar_eq,ite_eq_right hprim,zero_mul]

 theorem primary_angular_smalltwist_euler {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hr : r ≠ 0) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (ℓ : ℤ) (hu : AngularUnitCompatible d ψ ℓ)
    (hη : AngularUnitCompatible r η ℓ)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x))
    (W : ℝ → ℂ) (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) (t : ℝ) :
    (∑' x : Eisenstein, if primary x then
      mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)*theta ℓ x*
        mellinPhase t (norm x)*W (norm x/Z) else 0) =
      ∑ T ∈ (idealExponentOf (3*r)).support.powerset,
        (-1:ℂ)^T.card*angularResidueIdealChar d ψ ℓ (primeSetExponent T)*
          mellinPhase t (idealExponentNorm (primeSetExponent T))*
          ∑' ν, angularResidueIdealChar d ψ ℓ ν*mellinPhase t (idealExponentNorm ν)*
            W (idealExponentNorm ν/(Z/idealExponentNorm (primeSetExponent T))) := by
  let χ (ν : EisensteinIdealExponent) :=
    primaryMixedIdealChar a b ν*angularResidueIdealChar r η ℓ ν*mellinPhase t (idealExponentNorm ν)
  have he : (∑' x : Eisenstein, if primary x then
      mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)*theta ℓ x*
        mellinPhase t (norm x)*W (norm x/Z) else 0) =
      ∑' ν, χ ν*W (idealExponentNorm ν/Z) := by
    have hh := primary_element_ideal_smooth_eq χ W hW hZ
    have hleft : (∑' x : Eisenstein, if primary x then
        mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)*theta ℓ x*
          mellinPhase t (norm x)*W (norm x/Z) else 0) =
        ∑' x : Eisenstein, if primary x then χ (idealExponentOf x)*W (norm x/Z) else 0 := by
      apply tsum_congr
      intro x
      by_cases hx : primary x
      · rw [ite_eq_left hx,ite_eq_left hx]
        dsimp only [χ]
        rw [primaryMixedIdealChar_at_element ha hb hx,
          idealExponentOf_norm (primary_ne_zero hx),
          angularResidueIdealChar_at_element η hη (primary_ne_zero hx)]
        ring
      · rw [ite_eq_right hx,ite_eq_right hx]
    rw [hleft,hh]
    apply tsum_congr
    intro ν
    by_cases hν : primary (idealPrimaryGenerator ν)
    · rw [ite_eq_left hν]
    · rw [ite_eq_right hν]
      simp only [χ,primaryMixedIdealChar_eq,ite_eq_right hν,zero_mul]
  rw [he]
  let ω (ν : EisensteinIdealExponent) := angularResidueIdealChar d ψ ℓ ν*mellinPhase t (idealExponentNorm ν)
  have hω (ν κ : EisensteinIdealExponent) : ω (ν+κ) = ω ν*ω κ := by
    dsimp only [ω]
    rw [angularResidueIdealChar_add,idealExponentNorm_add,
      mellinPhase_mul_pos t (idealExponentNorm_pos ν) (idealExponentNorm_pos κ)]
    ring
  have hf : (∑' ν, χ ν*W (idealExponentNorm ν/Z)) =
      ∑' ν, if ∀ p ∈ (idealExponentOf (3*r)).support, ν p = 0 then
        ω ν*W (idealExponentNorm ν/Z) else 0 := by
    apply tsum_congr
    intro ν
    dsimp only [χ,ω]
    rw [angular_twisted_residue_restriction ha hb hsa hsb hab hr hsmall ψ η ℓ hu hη hagree]
    split <;> simp
  rw [hf]
  simpa only [ω,mul_assoc] using smooth_ideal_euler_exclusion
    (idealExponentOf (3*r)).support ω hω W hW hZ

end CubicFirstMoment

end

end OAI
