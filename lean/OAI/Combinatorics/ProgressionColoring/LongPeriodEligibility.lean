import OAI.Combinatorics.ProgressionColoring.LongPeriodRegularGrid
import OAI.Combinatorics.ProgressionColoring.AnchoredPatternDefinitions

namespace OAI

/-!
# Literal eligibility of a heavy long-period block

The actual interval labels are injective along a primitive short-drift block.
The regular-position count and stationary drift conditions are proved from
the rational grid and adaptive mesh, respectively.
-/

namespace QuantitativeVanDerWaerden

open AnchoredPatterns

/-- Primitive rational motion separates the literal first-coordinate mesh
labels throughout a full block, including all irregular positions. -/
theorem full_block_fullLabel_injective {D h : ℕ}
    (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (R : Realization D)
    (lambda : ℕ) (t : Fin D → Fin h) (hh : 0 < h)
    (hprimitive : PrimitiveVector h (fun i => ((t i).val : ℤ)))
    (hfirst : ∀ i, |R.u i| ≤ 1 / (n : ℝ))
    (hscale : 2 * (h : ℝ) * (1 / (n : ℝ)) < 1) :
    Function.Injective (fullLabel n hn A R lambda t) := by
  intro z w hlabel
  by_contra hne
  have hndvd : ¬ (h : ℤ) ∣ (z.val : ℤ) - w.val := by
    intro hdvd
    have hsmall : |(z.val : ℤ) - w.val| < (h : ℤ) := by
      apply abs_lt.mpr
      constructor <;> omega
    have heq := Int.eq_zero_of_abs_lt_dvd hdvd hsmall
    have hzw : z.val = w.val := by exact_mod_cast sub_eq_zero.mp heq
    exact hne (Fin.ext hzw)
  let X : ℕ → Fin D → ℝ := fun j i =>
    Int.fract (R.x i + (j : ℝ) / h * ((t i).val + R.u i))
  have hpath : ∀ j, j < h → ∀ i, ∃ e : ℤ,
      X j i - R.x i - (j : ℝ) / h *
        ((((t i).val : ℤ) : ℝ) + R.u i) = e := by
    intro j _ i
    refine ⟨-⌊R.x i + (j : ℝ) / h * ((t i).val + R.u i)⌋, ?_⟩
    simp only [X, Int.fract, Int.cast_neg, Int.cast_natCast]
    ring
  have hdrift : ∀ i, (h : ℝ) * |R.u i| ≤ (h : ℝ) * (1 / (n : ℝ)) :=
    fun i => mul_le_mul_of_nonneg_left (hfirst i) (Nat.cast_nonneg h)
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hmargin : 1 / (n : ℝ) + ((h : ℝ) * (1 / (n : ℝ))) / h < 1 / (h : ℝ) := by
    rw [mul_div_cancel_left₀ _ hhR.ne']
    apply (lt_div_iff₀ hhR).mpr
    nlinarith
  obtain ⟨i, hi⟩ := rational_path_coordinate_separation X R.x R.u hh hprimitive
    hpath hdrift hmargin z.isLt w.isLt hndvd
  have hilabel : UniformMesh.label n hn (firstPath R t z i) =
      UniformMesh.label n hn (firstPath R t w i) :=
    congrArg (fun L => L.1 i) hlabel
  have hz := UniformMesh.label_mem n hn (firstPath R t z i)
  have hw := UniformMesh.label_mem n hn (firstPath R t w i)
  rw [← hilabel] at hw
  have hwidth : |X z.val i - X w.val i| ≤ 1 / (n : ℝ) := by
    change |Int.fract (firstPath R t z i) - Int.fract (firstPath R t w i)| ≤ _
    have hinterval :
        (((UniformMesh.label n hn (firstPath R t z i)).val : ℝ) + 1) / n -
          ((UniformMesh.label n hn (firstPath R t z i)).val : ℝ) / n = 1 / (n : ℝ) := by
      ring
    apply abs_le.mpr
    constructor <;> linarith [hz.1, hz.2, hw.1, hw.2]
  exact (not_lt_of_ge hwidth) hi

/-- Every actual block satisfying the return-path bounds and containing a
heavy anchor is eligible for the recorded-pattern family. Neither half-block
regularity, distinct labels, nor stationary widths are assumed. -/
theorem heavy_long_block_eligible {D h : ℕ}
    (n : ℕ) (hn : 0 < n) (A : AdaptiveMesh) (R : Realization D)
    (lambda : ℕ) (t : Fin D → Fin h) (hh : 0 < h) (hD : 3 ≤ D)
    (hprimitive : PrimitiveVector h (fun i => ((t i).val : ℤ)))
    (hfirst : ∀ i, |R.u i| ≤ 1 / (n : ℝ))
    (hscale : 2 * (h : ℝ) * (1 / (n : ℝ)) < 1)
    (hrotating : ∀ i, ¬ stationary lambda t i → |R.v i| ≤ A.H)
    (hnear : ∀ i, ¬ stationary lambda t i → |R.v i| < 1 / (1000 * (D : ℝ)))
    (hperiod : ∀ i, ¬ stationary lambda t i →
      D ^ 2 < h / Nat.gcd h (lambda * (t i).val))
    (anchor : Fin h) (M k : ℝ) (hsmall : 2 * M / k ≤ 1 / 16)
    (hheavy : ∀ i, stationary lambda t i → |R.v i| ≤
      (2 * M / k) * A.width (A.meshLabel (secondPath R lambda t anchor i))) :
    EligibleRealization n hn A (1 / (1000 * (D : ℝ))) lambda t R := by
  classical
  let rotating : Finset (Fin D) := Finset.univ.filter fun i => ¬ stationary lambda t i
  have hregular := long_block_regular_card_at_scale hh hD rotating
    (fun z i => secondPath R lambda t z i) R.y R.v
    (fun i => lambda * (t i).val)
    (by
      intro i _ z
      refine ⟨0, ?_⟩
      simp only [secondPath, Nat.cast_mul, Int.cast_zero]
      ring)
    (by intro i hi; exact hnear i (Finset.mem_filter.mp hi).2)
    (by intro i hi; exact hperiod i (Finset.mem_filter.mp hi).2)
  have hregular' : (h : ℝ) / 2 ≤
      ((regularPositions (1 / (1000 * (D : ℝ))) R lambda t).card : ℝ) := by
    have hpositions : regularPositions (1 / (1000 * (D : ℝ))) R lambda t =
        Finset.univ.filter (fun z : Fin h => ∀ i ∈ rotating,
          1 / (1000 * (D : ℝ)) ≤ rho (secondPath R lambda t z i)) := by
      ext z
      simp [regularPositions, regular, rotating]
    rw [hpositions]
    exact hregular
  refine ⟨?_, ?_, hfirst, hrotating, ?_⟩
  · have hr : (h : ℝ) ≤ 2 *
        ((regularPositions (1 / (1000 * (D : ℝ))) R lambda t).card : ℝ) := by
      linarith
    exact_mod_cast hr
  · intro z w _ _ heq
    exact full_block_fullLabel_injective n hn A R lambda t hh hprimitive hfirst hscale heq
  · intro i hi z _
    have hstationary : (h : ℤ) ∣ ((lambda * (t i).val : ℕ) : ℤ) := by
      exact_mod_cast hi
    apply stationary_full_block_width A (fun z => secondPath R lambda t z i)
      hh hstationary (y := R.y i) (v := R.v i) ?_ anchor ?_ z
    · intro w
      refine ⟨0, ?_⟩
      simp only [secondPath, Nat.cast_mul, Int.cast_natCast, Int.cast_mul, Int.cast_zero]
      ring
    · exact stationary_relative_width_threshold
        (A.width_pos (A.meshLabel (secondPath R lambda t anchor i))).le hsmall (hheavy i hi)

end QuantitativeVanDerWaerden

end OAI
