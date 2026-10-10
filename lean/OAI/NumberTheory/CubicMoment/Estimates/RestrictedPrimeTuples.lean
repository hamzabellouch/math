import OAI.NumberTheory.CubicMoment.Estimates.PrimeConvolutionBounds
import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerConvolution

namespace OAI

/-! Exact tuple collection with an arbitrary original product restriction.
This allows the large distinguished rows to retain their sharp support
when both convolutions are expanded. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma orderedConvolution_sum_restrict (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (R : Finset Eisenstein) (χ : Eisenstein → ℂ) :
    (∑ b ∈ R, orderedConvolution S w b*χ b) =
      ∑ f ∈ Fintype.piFinset S,
        if (∏ i, f i) ∈ R then (∏ i, w i (f i))*χ (∏ i, f i) else 0 := by
  have he : (∑ b ∈ R, orderedConvolution S w b*χ b) =
      ∑ b ∈ orderedConvolutionSupport S,
        orderedConvolution S w b*(if b ∈ R then χ b else 0) := by
    apply Finset.sum_congr_of_eq_on_inter
    · intro b _hb hout
      rw [orderedConvolution_eq_zero_of_not_mem S w hout,zero_mul]
    · intro b _hb hout
      simp only [hout,ite_false,mul_zero]
    · intro b hb _hbS
      rw [ite_eq_left hb]
  rw [he,orderedConvolution_sum]
  apply Finset.sum_congr rfl
  intro f _hf
  split_ifs <;> simp only [mul_zero]

lemma orderedConvolution_double_restrict (S : ι → Finset Eisenstein)
    (T : κ → Finset Eisenstein) (v : ι → Eisenstein → ℂ)
    (w : κ → Eisenstein → ℂ) (R : Finset Eisenstein)
    (U : Eisenstein → Finset Eisenstein) (K : Eisenstein → Eisenstein → ℂ) :
    (∑ r ∈ R, orderedConvolution S v r*
      ∑ u ∈ U r, orderedConvolution T w u*K r u) =
      ∑ f ∈ Fintype.piFinset S, ∑ g ∈ Fintype.piFinset T,
        if (∏ i, f i) ∈ R then
          if (∏ j, g j) ∈ U (∏ i, f i) then
            (∏ i, v i (f i))*(∏ j, w j (g j))*K (∏ i, f i) (∏ j, g j)
          else 0
        else 0 := by
  rw [orderedConvolution_sum_restrict]
  apply Finset.sum_congr rfl
  intro f _hf
  by_cases hr : (∏ i, f i) ∈ R
  · simp only [hr,ite_true]
    rw [orderedConvolution_sum_restrict,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _hg
    split_ifs <;> simp only [mul_zero,mul_assoc]
  · simp only [hr,ite_false,Finset.sum_const_zero]

end CubicFirstMoment

end

end OAI
