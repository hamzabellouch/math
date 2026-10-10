import OAI.NumberTheory.TotientAsymptotic.PairedComparisonGrid
import OAI.NumberTheory.TotientAsymptotic.PPTNormalizedParameters

namespace OAI

/-!
The PPT first cutoff approaches the head coordinate.  Its lower head
edge must therefore vary with the available inverse-cube gap.  Interior
grid intervals and their finite labels are the same as in the ordinary
comparison grid.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def pptGridLower {b : ℕ} (δ θ : ℝ) (n : Fin b → ℕ) (j : ℕ) : ℝ :=
  if j = 0 then θ else pairedGridLower δ n j

/-- Every adaptive interval contains both actual coordinates.  The
top lower edge is chosen inside the true head-to-tail gap. -/
theorem ppt_grid_intervals {b : ℕ} {δ ζ θ : ℝ} (hb : 1 ≤ b) (hδ : 0 < δ)
    (u v : Fin b → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (halign : ∀ j, |u j-v j| ≤ (2*(j.val : ℝ)+1)*δ)
    (htop : max (u ⟨0,hb⟩) (v ⟨0,hb⟩) ≤ 1)
    (hhead : θ ≤ min (u ⟨0,hb⟩) (v ⟨0,hb⟩)) (hθ : θ < 1)
    (hfirst : pairedGridUpper δ ζ (fun j => collisionGridIndex δ (u j) (v j)) 1 < θ)
    (hnext : ∀ j : Fin b, ∀ hj : j.val+1 < b,
      max (u ⟨j.val+1,hj⟩) (v ⟨j.val+1,hj⟩)+(2*(j.val+1 : ℕ)+4 : ℝ)*δ <
        min (u j) (v j))
    (hbottom : ζ+δ < min (u ⟨b-1,by omega⟩) (v ⟨b-1,by omega⟩)) :
    let n := fun j => collisionGridIndex δ (u j) (v j)
    pairedGridUpper δ ζ n 0 = 1 ∧ pairedGridUpper δ ζ n b = ζ ∧
    (∀ j : Fin b, pptGridLower δ θ n j ≤ u j ∧ pptGridLower δ θ n j ≤ v j ∧
      u j ≤ pairedGridUpper δ ζ n j ∧ v j ≤ pairedGridUpper δ ζ n j) ∧
    (∀ j ∈ Finset.range b,
      pairedGridUpper δ ζ n (j+1) < pptGridLower δ θ n j ∧
        pptGridLower δ θ n j < pairedGridUpper δ ζ n j) := by
  dsimp only
  let n := fun j => collisionGridIndex δ (u j) (v j)
  have henc (j : Fin b) := collision_grid_enclosure hδ (hu j) (hv j) (halign j)
  have hlo (j : Fin b) := collision_grid_lower_bounds hδ (hu j) (hv j)
  refine ⟨by simp [pairedGridUpper],
    by simp [pairedGridUpper, show b ≠ 0 by omega], ?_, ?_⟩
  · intro j
    by_cases hj0 : j.val = 0
    · have he : j = ⟨0,hb⟩ := Fin.ext hj0
      subst j
      simp only [pptGridLower, pairedGridUpper, ite_true]
      exact ⟨hhead.trans (min_le_left _ _), hhead.trans (min_le_right _ _),
        (le_max_left _ _).trans htop, (le_max_right _ _).trans htop⟩
    · simp only [pptGridLower, pairedGridLower, pairedGridUpper, hj0, ite_false,
        dite_eq_left j.isLt]
      exact ⟨(henc j).1, (henc j).2.1, (henc j).2.2.1.le, (henc j).2.2.2.1.le⟩
  · intro j hj
    have hjb := Finset.mem_range.mp hj
    by_cases hj0 : j = 0
    · subst j
      simp only [pptGridLower, pairedGridUpper, ite_true]
      exact ⟨hfirst, hθ⟩
    · simp only [pptGridLower, pairedGridLower, hj0, ite_false, dite_eq_left hjb]
      constructor
      · by_cases hjn : j+1 < b
        · have he := collision_grid_separated hδ (hu ⟨j,hjb⟩) (hv ⟨j,hjb⟩)
            (hu ⟨j+1,hjn⟩) (hv ⟨j+1,hjn⟩) (halign ⟨j+1,hjn⟩)
            (hnext ⟨j,hjb⟩ hjn)
          simpa only [pairedGridUpper, Nat.add_eq_zero_iff, one_ne_zero,
            and_false, ite_false, dite_eq_left hjn] using he
        · have hlast : j = b-1 := by omega
          have heq : (⟨b-1,by omega⟩ : Fin b) = ⟨j,hjb⟩ := Fin.ext hlast.symm
          have hh : ζ+δ < min (u ⟨j,hjb⟩) (v ⟨j,hjb⟩) := by
            simpa only [heq] using hbottom
          have he : ζ < collisionGridLower δ (n ⟨j,hjb⟩) := by
            dsimp [n]
            linarith [(hlo ⟨j,hjb⟩).2]
          simpa only [pairedGridUpper, Nat.add_eq_zero_iff, one_ne_zero,
            and_false, ite_false, dite_eq_right hjn] using he
      · have hh := (henc ⟨j,hjb⟩).1.trans_lt (henc ⟨j,hjb⟩).2.2.1
        simpa only [pairedGridUpper, hj0, ite_false, dite_eq_left hjb] using hh

lemma ppt_grid_width {b : ℕ} (δ ζ θ : ℝ) (n : Fin b → ℕ)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 (b-1)) :
    pairedGridUpper δ ζ n j-pptGridLower δ θ n j = (2*(j : ℝ)+3)*δ := by
  have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  simpa only [pptGridLower, ite_eq_right hj0] using paired_grid_width δ ζ n hj

/-- The constructed finite intervals satisfy the literal published
parameter restrictions once their actual first-cutoff loss and scalar
size bounds are known. -/
theorem ppt_ford_parameters_from_grid {b : ℕ} {z S δ ζ θ : ℝ}
    (hb : 1 ≤ b) (hz : 1 < z) (hB : 0 < B z) (D r : ℕ)
    (n : Fin b → ℕ) (hS : Real.exp (Real.exp 1) ≤ S)
    (hSb : S ≤ comparisonCutoffs z (pairedGridUpper δ ζ n) b)
    (horder : ∀ j ∈ Finset.range b,
      pairedGridUpper δ ζ n (j+1) < pptGridLower δ θ n j ∧
        pptGridLower δ θ n j < pairedGridUpper δ ζ n j)
    (hfirst : Real.log (10*B z) ≤ B z*(1-pairedGridUpper δ ζ n 1))
    (hgap : ∀ j ∈ Finset.Icc 2 b,
      2*Real.sqrt (B S/B z) < pairedGridUpper δ ζ n (j-1)-pairedGridUpper δ ζ n j)
    (hD : 1 ≤ D) (hDz : (D : ℝ) ≤ z^(1/100 : ℝ))
    (hDs : (largestPrimeFactor D : ℝ) ≤ comparisonCutoffs z (pairedGridUpper δ ζ n) b)
    (hr : 1 ≤ r) (hrz : (r : ℝ) ≤ z^(1/10 : ℝ)) :
    FordComparisonParameters b z S D r
      (comparisonCutoffs z (pairedGridUpper δ ζ n))
      (comparisonCutoffs z (pptGridLower δ θ n)) := by
  exact ppt_ford_parameters_of_normalized_grid hz hB b D r S
    (pairedGridUpper δ ζ n) (pptGridLower δ θ n) hb
    (by simp [pairedGridUpper]) hS hSb horder hfirst hgap hD hDz hDs hr hrz

end TotientAsymptotic

end

end OAI
