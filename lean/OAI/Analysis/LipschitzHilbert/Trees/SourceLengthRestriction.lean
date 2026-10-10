import OAI.Analysis.LipschitzHilbert.Estimates.StoppingScaleIntervals

namespace OAI

/-! Restricting to an interval of original packet lengths preserves all
interval concentration bounds. The resulting coefficients are explicit
zero extensions of the original analyzing coefficients. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice

attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

def restrictCoefficient (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lower upper : ℕ) (j : Fin N) (l : P.labels j) (u : Item j l) : EuclideanSpace ℂ κ :=
  if lower ≤ j.val ∧ j.val < upper then coeff j l u else 0

theorem rawBand_restrictCoefficient (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lower upper : ℕ) (jet : Fin 3) (j : Fin N) (x y : ℝ) :
    P.rawBand (P.restrictCoefficient coeff lower upper) jet j x y =
      if lower ≤ j.val ∧ j.val < upper then P.rawBand coeff jet j x y else 0 := by
  by_cases hj : lower ≤ j.val ∧ j.val < upper
  · simp [rawBand, restrictCoefficient, hj]
  · simp only [rawBand, restrictCoefficient, hj, ite_false]
    ext k
    simp only [vectorPacketSynthesis, packetSynthesis_apply, PiLp.zero_apply,
      zero_mul, Finset.sum_const_zero]

theorem restricted_rawInterval_eq (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lengthLower lengthUpper : ℕ) (jet : Fin 3) (lower upper : ℕ)
    (hlu : lower ≤ upper) (hu : upper ≤ N) (x y : ℝ) :
    ∃ l u : ℕ, l ≤ u ∧ u ≤ N ∧
      P.rawInterval (P.restrictCoefficient coeff lengthLower lengthUpper) jet lower upper x y =
        P.rawInterval coeff jet l u x y := by
  let l := min N (max lower lengthLower)
  let u := max l (min upper lengthUpper)
  have hlN : l ≤ N := min_le_left _ _
  have hlu' : l ≤ u := le_max_left _ _
  have huN : u ≤ N := max_le hlN ((min_le_left _ _).trans hu)
  refine ⟨l,u,hlu',huN,?_⟩
  rw [P.rawInterval_eq_band_sum _ jet lower upper hlu x y,
    P.rawInterval_eq_band_sum _ jet l u hlu' x y]
  simp_rw [P.rawBand_restrictCoefficient]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  dsimp only [l,u]
  have hjN := j.isLt
  omega

/-- Every restricted source interval is an original interval, including
when the two length ranges are disjoint. -/
theorem restricted_rawInterval_bound (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lengthLower lengthUpper : ℕ) (jet : Fin 3) (x y B : ℝ)
    (hbound : ∀ lower upper, lower ≤ upper → upper ≤ N →
      ‖P.rawInterval coeff jet lower upper x y‖ ≤ B) :
    ∀ lower upper, lower ≤ upper → upper ≤ N →
      ‖P.rawInterval (P.restrictCoefficient coeff lengthLower lengthUpper)
        jet lower upper x y‖ ≤ B := by
  intro lower upper hlu hu
  obtain ⟨l,u,hlu',hu',heq⟩ := P.restricted_rawInterval_eq coeff lengthLower lengthUpper
    jet lower upper hlu hu x y
  rw [heq]
  exact hbound l u hlu' hu'

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
