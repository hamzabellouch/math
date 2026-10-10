import OAI.NumberTheory.CubicMoment.Estimates.SmallPrimeParts
import OAI.NumberTheory.CubicMoment.Estimates.ResidueProducts
import OAI.NumberTheory.CubicMoment.Estimates.LogSmoothWeights

namespace OAI

/-! Literal finite-character factorization at the small conductor primes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mixedCubic_modulus_mul {a₁ a₂ b₁ b₂ : Eisenstein}
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0)
    (x : Eisenstein) :
    mixedCubic (a₁*a₂) (b₁*b₂) x = mixedCubic a₁ b₁ x*mixedCubic a₂ b₂ x := by
  simp only [mixedCubic,cubicSymbol_mul_lower ha₁ ha₂,cubicSymbol_mul_lower hb₁ hb₂,star_mul]
  ring

lemma small_outside_mixedCubic (v : Eisenstein) {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (x : Eisenstein) :
    mixedCubic a b x = mixedCubic (primarySmallPart v a) (primarySmallPart v b) x*
      mixedCubic (primaryOutsidePart v a) (primaryOutsidePart v b) x := by
  conv_lhs => rw [← primary_small_outside_mul v ha,← primary_small_outside_mul v hb]
  exact mixedCubic_modulus_mul (primary_ne_zero (primarySmallPart_primary v ha))
    (primary_ne_zero (primaryOutsidePart_primary v ha))
    (primary_ne_zero (primarySmallPart_primary v hb))
    (primary_ne_zero (primaryOutsidePart_primary v hb)) x

def smallPartResidueTwist (v a b q : Eisenstein) (ha : primary a) (hb : primary b)
    (η : MulChar (Residues q) ℂ) :
    MulChar (Residues ((3*(primarySmallPart v a*primarySmallPart v b))*q)) ℂ :=
  productResidueChar
    (primaryMixedResidueChar (primarySmallPart v a) (primarySmallPart v b) (primarySmallPart_primary v ha) (primarySmallPart_primary v hb)) η

lemma smallPartResidueTwist_units (v : Eisenstein) {a b q : Eisenstein}
    (ha : primary a) (hb : primary b) (η : MulChar (Residues q) ℂ)
    (hη : ∀ u : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) u) = 1) :
    ∀ u : Eisensteinˣ, smallPartResidueTwist v a b q ha hb η
      (Ideal.Quotient.mk (modulus ((3*(primarySmallPart v a*primarySmallPart v b))*q)) u) = 1 :=
  productResidueChar_units _ _
    (primaryMixedResidueChar_trivialInfinity (primarySmallPart_primary v ha) (primarySmallPart_primary v hb)) hη

lemma smallPartResidueTwist_primary (v : Eisenstein) {a b q x : Eisenstein}
    (ha : primary a) (hb : primary b) (hx : primary x) (η : MulChar (Residues q) ℂ) :
    mixedCubic a b x*η (Ideal.Quotient.mk (modulus q) x) =
      mixedCubic (primaryOutsidePart v a) (primaryOutsidePart v b) x*
      smallPartResidueTwist v a b q ha hb η
        (Ideal.Quotient.mk (modulus ((3*(primarySmallPart v a*primarySmallPart v b))*q)) x) := by
  rw [small_outside_mixedCubic v ha hb]
  simp only [smallPartResidueTwist,productResidueChar_mk,
    primaryMixedResidueChar_primary (primarySmallPart_primary v ha) (primarySmallPart_primary v hb) hx]
  ring

lemma primarySmallTwistSmoothSum_small_parts (v : Eisenstein) {a b q : Eisenstein}
    (ha : primary a) (hb : primary b) (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ) (Z t : ℝ) :
    primarySmallTwistSmoothSum a b q η W Z t =
      primarySmallTwistSmoothSum (primaryOutsidePart v a) (primaryOutsidePart v b)
        ((3*(primarySmallPart v a*primarySmallPart v b))*q)
        (smallPartResidueTwist v a b q ha hb η) W Z t := by
  unfold primarySmallTwistSmoothSum
  apply tsum_congr
  intro x
  by_cases hx : primary x
  · simp only [ite_eq_left hx,smallPartResidueTwist_primary v ha hb hx η]
  · simp only [ite_eq_right hx]

lemma primaryOutsidePart_injOn_small_fiber (v s : Eisenstein) (P : Finset Eisenstein)
    (hP : ∀ a ∈ P, primary a) :
    Set.InjOn (primaryOutsidePart v) ↑(P.filter (fun a => primarySmallPart v a = s)) := by
  intro a ha b hb he
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  rw [← primary_small_outside_mul v (hP a ha'.1),← primary_small_outside_mul v (hP b hb'.1),
    ha'.2,hb'.2,he]

lemma primaryOutsidePart_norm_le (v : Eisenstein) {a : Eisenstein} (ha : primary a) :
    norm (primaryOutsidePart v a) ≤ norm a := by
  apply norm_le_of_dvd (primary_ne_zero ha)
  exact ⟨primarySmallPart v a,by rw [mul_comm,primary_small_outside_mul v ha]⟩

lemma primaryOutsidePart_norm_lower (v : Eisenstein) {a : Eisenstein}
    (ha : primary a) (hsa : Squarefree a) (hv : v ≠ 0) :
    norm a/norm v ≤ norm (primaryOutsidePart v a) := by
  have hs := norm_le_of_dvd hv (primarySmallPart_dvd hsa hv)
  have hp := congrArg norm (primary_small_outside_mul v ha)
  rw [norm_mul_eq] at hp
  apply (div_le_iff₀ (norm_pos_of_ne_zero hv)).mpr
  rw [mul_comm]
  nlinarith [norm_nonneg (primaryOutsidePart v a)]

end CubicFirstMoment

end

end OAI
