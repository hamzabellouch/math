import OAI.NumberTheory.CubicMoment.Estimates.TwistedIdealMatch

namespace OAI

/-! Exact Euler restoration for the small-twisted primary sum. Only the
primes above three and the fixed small modulus are omitted. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma twisted_residue_restriction {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hr : r ≠ 0) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (hu : ∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1)
    (hη : ∀ u : Eisensteinˣ, η (Ideal.Quotient.mk (modulus r) u) = 1)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x))
    (ν : EisensteinIdealExponent) :
    primaryMixedIdealChar a b ν*residueIdealChar r η ν =
      if ∀ p ∈ (idealExponentOf (3*r)).support, ν p = 0 then residueIdealChar d ψ ν else 0 := by
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
    exact (twisted_ideal_mixed_match ha hb hsa hsb hab hsmall ψ η hu hη hagree ν hprim hpr).symm
  · rw [ite_eq_right hlocal]
    by_cases hprim : primary (idealPrimaryGenerator ν)
    · have hn : ¬ IsCoprime r (idealExponentGenerator ν) := by
        intro hc
        apply hlocal
        apply (ideal_coprime_support h3r ν).mp
        exact ((idealGenerator_coprime_three_iff ν).mpr
          ((idealPrimaryGenerator_primary_iff ν).mp hprim)).symm.mul_left hc
      have hz : residueIdealChar r η ν = 0 :=
        MulChar.map_nonunit η (fun h => hn (isCoprime_of_residue_isUnit h))
      rw [hz,mul_zero]
    · rw [primaryMixedIdealChar_eq,ite_eq_right hprim,zero_mul]

 theorem primary_smalltwist_euler {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hr : r ≠ 0) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (hu : ∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1)
    (hη : ∀ u : Eisensteinˣ, η (Ideal.Quotient.mk (modulus r) u) = 1)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x))
    (W : ℝ → ℂ) (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) (t : ℝ) :
    (∑' x : Eisenstein, if primary x then
      mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)*
        mellinPhase t (norm x)*W (norm x/Z) else 0) =
      ∑ T ∈ (idealExponentOf (3*r)).support.powerset,
        (-1:ℂ)^T.card*residueIdealChar d ψ (primeSetExponent T)*
          mellinPhase t (idealExponentNorm (primeSetExponent T))*
          ∑' ν, residueIdealChar d ψ ν*mellinPhase t (idealExponentNorm ν)*
            W (idealExponentNorm ν/(Z/idealExponentNorm (primeSetExponent T))) := by
  let χ (ν : EisensteinIdealExponent) :=
    primaryMixedIdealChar a b ν*residueIdealChar r η ν*mellinPhase t (idealExponentNorm ν)
  have he : (∑' x : Eisenstein, if primary x then
      mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)*
        mellinPhase t (norm x)*W (norm x/Z) else 0) =
      ∑' ν, χ ν*W (idealExponentNorm ν/Z) := by
    have hh := primary_element_ideal_smooth_eq χ W hW hZ
    have hleft : (∑' x : Eisenstein, if primary x then
        mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)*
          mellinPhase t (norm x)*W (norm x/Z) else 0) =
        ∑' x : Eisenstein, if primary x then χ (idealExponentOf x)*W (norm x/Z) else 0 := by
      apply tsum_congr
      intro x
      by_cases hx : primary x
      · rw [ite_eq_left hx,ite_eq_left hx]
        dsimp only [χ]
        rw [primaryMixedIdealChar_at_element ha hb hx,
          idealExponentOf_norm (primary_ne_zero hx),
          residueIdealChar_primaryNormalize η hη,idealPrimaryGenerator_at_element hx]
      · rw [ite_eq_right hx,ite_eq_right hx]
    rw [hleft,hh]
    apply tsum_congr
    intro ν
    by_cases hν : primary (idealPrimaryGenerator ν)
    · rw [ite_eq_left hν]
    · rw [ite_eq_right hν]
      simp only [χ,primaryMixedIdealChar_eq,ite_eq_right hν,zero_mul]
  rw [he]
  let ω (ν : EisensteinIdealExponent) := residueIdealChar d ψ ν*mellinPhase t (idealExponentNorm ν)
  have hω (ν κ : EisensteinIdealExponent) : ω (ν+κ) = ω ν*ω κ := by
    dsimp only [ω]
    rw [residueIdealChar_add,idealExponentNorm_add,
      mellinPhase_mul_pos t (idealExponentNorm_pos ν) (idealExponentNorm_pos κ)]
    ring
  have hf : (∑' ν, χ ν*W (idealExponentNorm ν/Z)) =
      ∑' ν, if ∀ p ∈ (idealExponentOf (3*r)).support, ν p = 0 then
        ω ν*W (idealExponentNorm ν/Z) else 0 := by
    apply tsum_congr
    intro ν
    dsimp only [χ,ω]
    rw [twisted_residue_restriction ha hb hsa hsb hab hr hsmall ψ η hu hη hagree]
    split <;> simp
  rw [hf]
  simpa only [ω,mul_assoc] using smooth_ideal_euler_exclusion
    (idealExponentOf (3*r)).support ω hω W hW hZ

end CubicFirstMoment

end

end OAI
