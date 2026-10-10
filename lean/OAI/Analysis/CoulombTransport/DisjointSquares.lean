import OAI.Analysis.CoulombTransport.Model

namespace OAI

universe uIndex uX

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem356

/-- Disjoint nonnegative summands allow the square root of a weighted sum of
squares to be written without any nonsmooth square-root composition. -/
theorem sqrt_sum_disjoint_squares {ι : Type uIndex} {X : Type uX} (s : Finset ι)
    (a : ι → ℝ) (g : ι → X → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (x : X) :
    Real.sqrt (∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, Real.sqrt (a i) * g i x := by
  classical
  by_cases h : ∃ i ∈ s, g i x ≠ 0
  · obtain ⟨i, hi, hix⟩ := h
    have hz : ∀ j ∈ s, j ≠ i → g j x = 0 := by
      intro j hj hji
      by_contra hjx
      exact Set.disjoint_left.mp (hd i hi j hj hji.symm) hix hjx
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
    · rw [Real.sqrt_mul (ha i hi), Real.sqrt_sq (hg i hi x)]
    · intro j hj hji
      simp [hz j hj hji]
    · exact fun hni => False.elim (hni hi)
    · intro j hj hji
      simp [hz j hj hji]
    · exact fun hni => False.elim (hni hi)
  · have hz : ∀ i ∈ s, g i x = 0 := by
      intro i hi
      by_contra hix
      exact h ⟨i, hi, hix⟩
    have hleft : (∑ i ∈ s, a i * (g i x) ^ 2) = 0 :=
      Finset.sum_eq_zero (fun i hi => by simp [hz i hi])
    have hright : (∑ i ∈ s, Real.sqrt (a i) * g i x) = 0 :=
      Finset.sum_eq_zero (fun i hi => by simp [hz i hi])
    rw [hleft, hright, Real.sqrt_zero]

/-- A finite disjoint family of smooth compactly supported nonnegative square
roots yields a density satisfying both smoothness requirements of the target. -/
theorem isSmoothCompactProbabilityDensity_sum_disjoint_squares {ι : Type uIndex}
    (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hsm : ∀ i ∈ s, ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (g i))
    (hcs : ∀ i ∈ s, HasCompactSupport (g i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (hmass : (∫ x : E3, (∑ i ∈ s, a i * (g i x) ^ 2)
      ∂(volume : Measure E3)) = 1) :
    IsSmoothCompactProbabilityDensity (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) := by
  have hsqrt : (fun x => Real.sqrt (∑ i ∈ s, a i * (g i x) ^ 2)) =
      (fun x => ∑ i ∈ s, Real.sqrt (a i) * g i x) := by
    funext x
    exact sqrt_sum_disjoint_squares s a g ha hg hd x
  refine ⟨?_, ?_, ?_, ?_, ?_, hmass⟩
  · intro x
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _))
  · exact ContDiff.sum (fun i hi => contDiff_const.mul ((hsm i hi).pow 2))
  · have hterm : ∀ i ∈ s, HasCompactSupport (fun x => a i * (g i x) ^ 2) := by
      intro i hi
      simpa only [Function.comp_def] using
        (hcs i hi).comp_left (g := fun y : ℝ => a i * y ^ 2) (by simp)
    simpa only [Finset.sum_fn] using HasCompactSupport.finset_sum hterm
  · rw [hsqrt]
    exact ContDiff.sum (fun i hi => contDiff_const.mul (hsm i hi))
  · rw [hsqrt]
    have hterm : ∀ i ∈ s, HasCompactSupport (fun x => Real.sqrt (a i) * g i x) := by
      intro i hi
      simpa only [Function.comp_def] using
        (hcs i hi).comp_left (g := fun y : ℝ => Real.sqrt (a i) * y) (by simp)
    simpa only [Finset.sum_fn] using HasCompactSupport.finset_sum hterm

/-- Convenient normalization form for the five component densities: every
square has unit mass, and the component weights sum to one. -/
theorem isSmoothCompactProbabilityDensity_sum_normalized_disjoint_squares
    {ι : Type uIndex} (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hsm : ∀ i ∈ s, ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (g i))
    (hcs : ∀ i ∈ s, HasCompactSupport (g i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (hgint : ∀ i ∈ s, (∫ x : E3, (g i x) ^ 2 ∂(volume : Measure E3)) = 1)
    (haint : (∑ i ∈ s, a i) = 1) :
    IsSmoothCompactProbabilityDensity (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) := by
  apply isSmoothCompactProbabilityDensity_sum_disjoint_squares s a g ha hg hsm hcs hd
  have hint : ∀ i ∈ s, Integrable (fun x => a i * (g i x) ^ 2)
      (volume : Measure E3) := by
    intro i hi
    have hcomp : HasCompactSupport (fun x => (g i x) ^ 2) := by
      simpa only [Function.comp_def] using
        (hcs i hi).comp_left (g := fun y : ℝ => y ^ 2) (by simp)
    exact ((hsm i hi).continuous.pow 2).integrable_of_hasCompactSupport hcomp |>.const_mul (a i)
  rw [integral_finsetSum s hint]
  calc
    (∑ i ∈ s, ∫ x : E3, a i * (g i x) ^ 2 ∂(volume : Measure E3)) =
        ∑ i ∈ s, a i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul, hgint i hi, mul_one]
    _ = 1 := haint

/-- The density assembled from weighted squares represents the corresponding
finite mixture of component measures. No disjointness is needed here. -/
theorem densityMeasure_sum_weighted_squares {ι : Type uIndex}
    (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hgm : ∀ i ∈ s, Measurable (g i)) :
    densityMeasure (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, ENNReal.ofReal (a i) • densityMeasure (fun x => (g i x) ^ 2) := by
  have hpoint : ∀ x, ENNReal.ofReal (∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, ENNReal.ofReal (a i) * ENNReal.ofReal ((g i x) ^ 2) := by
    intro x
    rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _))]
    exact Finset.sum_congr rfl (fun i hi => ENNReal.ofReal_mul (ha i hi))
  ext A hA
  simp only [Measure.finsetSum_apply, Measure.smul_apply, densityMeasure,
    withDensity_apply _ hA, smul_eq_mul]
  simp_rw [hpoint]
  rw [lintegral_finsetSum s (f := fun i x => ENNReal.ofReal (a i) * ENNReal.ofReal ((g i x) ^ 2))
    (fun i hi => measurable_const.mul ((hgm i hi).pow_const 2).ennreal_ofReal)]
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_const_mul _ ((hgm i hi).pow_const 2).ennreal_ofReal

end Problem356

end

end OAI
