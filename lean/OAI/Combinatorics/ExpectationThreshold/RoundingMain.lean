import OAI.Combinatorics.ExpectationThreshold.RoundingMasses
import OAI.Combinatorics.ExpectationThreshold.RoundingLowerBound
import OAI.Combinatorics.ExpectationThreshold.RoundingProbabilityContradiction
import OAI.Combinatorics.ExpectationThreshold.ColorMean
import OAI.Combinatorics.ExpectationThreshold.SelectorMain

namespace OAI

/-!
# Actual rounding of an unrestricted fractional cover

The concrete member masses feed the proved multiscale selector. The same
independent color law supplies the lower and upper bounds on the subset-product
score. No selector hypothesis or bound on support sizes appears in the result.
-/

open scoped BigOperators

noncomputable section

namespace TalagrandThreshold

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem fractionalCover_empty_not_mem {F : Family α} {g : Finset α → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hcover : FractionalCover F g) (hcost : fracCost r g ≤ 1 / 2) :
    (∅ : Finset α) ∉ F := by
  intro hempty
  have hcoverEmpty : (1 : ℝ) ≤ g ∅ := by
    simpa only [Finset.powerset_empty, Finset.sum_singleton] using hcover.2 ∅ hempty
  have hweight : g ∅ ≤ (1 / 2 : ℝ) :=
    (empty_weight_le_fracCost hr hcover.nonneg).trans hcost
  exact (by norm_num : ¬ ((1 : ℝ) ≤ 1 / 2)) (hcoverEmpty.trans hweight)

/-- The actual normalized probability masses attached to family members. -/
def fractionalMassFamily (F : Family α) (g : Finset α → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hcover : FractionalCover F g) (hcost : fracCost r g ≤ 1 / 2) :
    Selector.MassFamily F where
  weight H := roundingMass g H.val
  nonneg H x := roundingMass_nonneg g H.val hcover.nonneg
    (memberMass_pos_of_fractionalCover hcover H.property hr hcost) x
  total H := roundingMass_sum g H.val
    (memberMass_pos_of_fractionalCover hcover H.property hr hcost)
  supported H _ hx := roundingMass_eq_zero_of_not_mem g H.val hx

/-- Every fractional cover of cost at most one half rounds at the exact
parameter `r / (25 * 512^4)`. Its support may contain subsets of any size. -/
theorem fractionalCover_rounding (F : Family α) (g : Finset α → ℝ) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hcover : FractionalCover F g)
    (hcost : fracCost r g ≤ 1 / 2) :
    Small (r / ((25 : ℝ) * (512 : ℝ) ^ 4)) F := by
  classical
  by_cases hF : F.Nonempty
  · let p : ℝ := r / ((25 : ℝ) * (512 : ℝ) ^ 4)
    have hp0 : 0 < p := div_pos hr0 rounding_constant_pos
    have hp1 : p ≤ 1 := (div_le_one rounding_constant_pos).mpr
      (hr1.trans (by norm_num : (1 : ℝ) ≤ (25 : ℝ) * (512 : ℝ) ^ 4))
    have hnoempty := fractionalCover_empty_not_mem hr0.le hcover hcost
    let mu := fractionalMassFamily F g hr0.le hcover hcost
    obtain ⟨s, hs, hnext⟩ := exists_scale hp0
    let μ := coloringLaw (α := α) p s hp0 hs
    let Y : Color s → ℝ := fun c => (512 : ℝ) ^ 4 / (512 : ℝ) ^ (c.val + 1)
    let Z : Coloring α s → ℝ := fun a => productScore g (fun x => Y (a x))
    let P : Coloring α s → Prop := fun a => ∃ H : ↥F, Selector.meanColor mu H a ≤ 2
    change Small p F
    by_contra hnotsmall
    have hprob : (9 / 10 : ℝ) ≤ μ.prob P :=
      Selector.average_color F hF (fun H hH => members_nonempty hnoempty hH)
        mu p hp0 hp1 hnotsmall s hs
    have hY : ∀ c, 0 ≤ Y c := by
      intro c
      exact div_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
    have hZ : ∀ a, 0 ≤ Z a := fun a =>
      productScore_nonneg hcover.nonneg (fun x => hY (a x))
    have hlower : ∀ a, P a → (1 / 4 : ℝ) ≤ Z a := by
      intro a ha
      obtain ⟨H, hH⟩ := ha
      apply productScore_lower_of_mean g H.val (fun x => (a x).val + 1) hcover.nonneg
        (memberMass_ge_half hcover H.property hr0.le hcost)
      simpa only [Selector.meanColor, mu, fractionalMassFamily, Nat.cast_add,
        Nat.cast_one] using hH
    have hmean : (colorLaw p s hp0 hs).expectation Y ≤ r / 5 := by
      change (∑ c : Color s,
        colorProb p s c * ((512 : ℝ) ^ 4 / (512 : ℝ) ^ (c.val + 1))) ≤ r / 5
      exact color_mean_le_r_div_five hr0 hs hnext
    have hupper : μ.expectation Z ≤ (1 / 10 : ℝ) :=
      expectation_productScore_le_tenth (colorLaw p s hp0 hs) g Y
        hcover.nonneg hY hr0.le hmean hcost
    exact rounding_expectation_contradiction μ P Z hZ hprob hlower hupper
  · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    rw [hFempty]
    exact small_empty _

/-- Parameterwise rounding also includes density zero, with an actual cover. -/
theorem fractionalSmall_rounding (F : Family α) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hF : FractionalSmall r F) :
    Small (r / ((25 : ℝ) * (512 : ℝ) ^ 4)) F := by
  obtain ⟨g, hcover, hcost⟩ := hF
  by_cases hr : r = 0
  · subst r
    rw [zero_div]
    exact small_zero F (fractionalCover_empty_not_mem le_rfl hcover hcost)
  · exact fractionalCover_rounding F g (lt_of_le_of_ne hr0 (Ne.symm hr)) hr1 hcover hcost

end TalagrandThreshold

end

end OAI
