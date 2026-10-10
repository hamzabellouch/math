import Mathlib
import OAI.Combinatorics.Chromatic.Walls.HNRestrictionOrder

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
variable (c η : I → ℝ) (hc : ∀ i,0<c i)
include hc

lemma clipped_equal_head (κ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hk : κ < slope c η (d₁+e₁)) (ht : slope c η (d₂+e₂) ≤ κ)
    (hd : d₁+d₂≠0) (hs : slope c η (d₁+e₁) ≤ slope c η (d₁+d₂))
    (hm : slope c η (d₁+d₂)=slope c η (d₁+e₁) → mass c (d₁+e₁) ≤ mass c (d₁+d₂))
    (hp : mass η d₁ ≤ clippedSlope c η κ (d₁+e₁)*mass c d₁)
    (hq : mass η d₂ ≤ clippedSlope c η κ (d₂+e₂)*mass c d₂) :
    e₁=0 ∧ d₂=0 := by
  rw [clippedSlope_of_ge c η hk.le] at hp
  rw [clippedSlope_of_le c η ht] at hq
  have hmass := mass_eq c η hc (d₁+d₂)
  have hsrc := mul_le_mul_of_nonneg_right hs (mass_nonneg c (fun i=>(hc i).le) (d₁+d₂))
  rw [←hmass,mass_add,mass_add] at hsrc
  have hz : d₂=0 := by
    by_contra hn
    have hpos:=mass_pos c hc d₂ hn
    have hh := mul_lt_mul_of_pos_right hk hpos
    nlinarith
  have hm' : mass c (d₁+e₁) ≤ mass c d₁ := by
    apply (by simpa only [hz,add_zero] using hm)
    apply le_antisymm _ (by simpa only [hz,add_zero] using hs)
    have hn : d₁≠0 := by simpa only [hz,add_zero] using hd
    exact (div_le_iff₀ (mass_pos c hc d₁ hn)).mpr hp
  rw [mass_add] at hm'
  refine ⟨?_,hz⟩
  by_contra hn
  have hp:=mass_pos c hc e₁ hn
  linarith

lemma clipped_head_destabilizes (κ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hk : κ < slope c η (d₁+e₁)) (ht : slope c η (d₂+e₂) ≤ κ)
    (hd : d₁+d₂≠0) (hs : slope c η (d₁+e₁) ≤ slope c η (d₁+d₂))
    (hm : slope c η (d₁+d₂)=slope c η (d₁+e₁) → mass c (d₁+e₁) ≤ mass c (d₁+d₂))
    (hne : ¬ (e₁=0 ∧ d₂=0)) :
    (d₁≠0 ∧ e₁≠0 ∧ clippedSlope c η κ (d₁+e₁)<clippedSlope c η κ d₁) ∨
    (d₂≠0 ∧ e₂≠0 ∧ clippedSlope c η κ (d₂+e₂)<clippedSlope c η κ d₂) := by
  by_cases hp : clippedSlope c η κ (d₁+e₁)*mass c d₁ < mass η d₁
  · exact Or.inl (clipped_high_mass c η hc κ d₁ e₁ hp)
  by_cases hq : clippedSlope c η κ (d₂+e₂)*mass c d₂ < mass η d₂
  · exact Or.inr (clipped_high_mass c η hc κ d₂ e₂ hq)
  exact (hne (clipped_equal_head c η hc κ d₁ e₁ d₂ e₂ hk ht hd hs hm
    (le_of_not_gt hp) (le_of_not_gt hq))).elim
end ElementaryPositivity.SlopeArithmetic

namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
include hc
lemma clipped_cell_nonhead_zero (κ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hk : κ < slope c η (d₁+e₁)) (ht : slope c η (d₂+e₂) ≤ κ)
    (hd : d₁+d₂≠0) (hs : slope c η (d₁+e₁) ≤ slope c η (d₁+d₂))
    (hm : slope c η (d₁+d₂)=slope c η (d₁+e₁) → mass c (d₁+e₁) ≤ mass c (d₁+d₂))
    (hne : ¬ (e₁=0 ∧ d₂=0))
    (p : MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ) :
    quotientTensor a (clippedSlope c η κ) (d₁+e₁) (d₂+e₂)
      (cellTransfer a d₁ e₁ d₂ e₂ p)=0 :=
  quotient_cellTransfer_zero a (clippedSlope c η κ) _ _ _ _
    (clipped_head_destabilizes c η hc κ d₁ e₁ d₂ e₂ hk ht hd hs hm hne) p
end ElementaryPositivity.RawShuffle

end

end OAI
