import OAI.Analysis.IrrationalRotation.Model.OneCoordinateConditional
import OAI.Analysis.IrrationalRotation.Analysis.FiniteKernelMixture
import OAI.Analysis.IrrationalRotation.Product.OneCoordinateDensity

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace Invariant233.OneCoordinateCoupling
open CouplingMixture CouplingMarginalBounds FiniteKernelMixture

private lemma finite_total (q : ℝ) (p : Fin 5 → ℝ) (u : Fin 5 → ℝ → ℝ) (x : ℝ) :
    ENNReal.ofReal q + ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (u i x) ≠ ∞ := by
  apply ENNReal.add_ne_top.mpr
  refine ⟨ENNReal.ofReal_ne_top, ENNReal.sum_ne_top.mpr ?_⟩
  intro i _
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

section SourceParameters
variable {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)
include hκ0 hκ hm ha ha' hb hb' ht0 ht

lemma rightGivenLeft_isMarkov : IsMarkovKernel (rightGivenLeft κ m a b t) := by
  have hm0 : 0 < m := by linarith
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) (width_pos hm0 ha) ha' (width_pos hm0 hb) hb'
  apply diagonalReplacementKernel_isMarkov
  · apply ENNReal.ofReal_ne_zero_iff.mpr
    have := (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
    linarith
  · exact finite_total _ _ _

lemma leftGivenRight_isMarkov : IsMarkovKernel (leftGivenRight κ m a b t) := by
  have hm0 : 0 < m := by linarith
  have : ∀ i, IsProbabilityMeasure (leftLaw m a b i) :=
    leftLaw_isProbabilityMeasure hm0 (width_pos hm0 ha) ha' (width_pos hm0 hb) hb'
  apply diagonalReplacementKernel_isMarkov
  · apply ENNReal.ofReal_ne_zero_iff.mpr
    have := (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
    linarith
  · exact finite_total _ _ _

lemma rightGivenLeft_disintegration :
    (pairLaw κ m a b t).fst ⊗ₘ rightGivenLeft κ m a b t = pairLaw κ m a b t := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have := rightGivenLeft_isMarkov hκ0 hκ hm ha ha' hb hb' ht0 ht
  have hq : ENNReal.ofReal (diagonalMass κ m a b t) ≠ 0 := by
    apply ENNReal.ofReal_ne_zero_iff.mpr
    have := (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
    linarith
  let d : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (diagonalMass κ m a b t) +
    ∑ i, ENNReal.ofReal (componentProbabilities κ m a b t i) *
      ENNReal.ofReal (leftDensity m a b i x)
  have hpair : (baseLaw.withDensity d) ⊗ₘ rightGivenLeft κ m a b t = pairLaw κ m a b t := by
    unfold rightGivenLeft d
    rw [diagonalReplacementKernel_disintegration _ _ hq]
    · unfold pairLaw mixture CouplingMixture.diagonal
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [leftLaw_eq_withDensity (by linarith) ha0 ha' hb0 hb']
    · exact finite_total _ _ _
  have hfst := congrArg Measure.fst hpair
  rw [Measure.fst_compProd] at hfst
  rw [← hfst]
  exact hpair

lemma leftGivenRight_disintegration :
    (pairLaw κ m a b t).snd ⊗ₘ leftGivenRight κ m a b t =
      (pairLaw κ m a b t).map Prod.swap := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (leftLaw m a b i) :=
    leftLaw_isProbabilityMeasure hm0 ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw m a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have := leftGivenRight_isMarkov hκ0 hκ hm ha ha' hb hb' ht0 ht
  have hq : ENNReal.ofReal (diagonalMass κ m a b t) ≠ 0 := by
    apply ENNReal.ofReal_ne_zero_iff.mpr
    have := (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
    linarith
  have hswap : (pairLaw κ m a b t).map Prod.swap =
      ENNReal.ofReal (diagonalMass κ m a b t) • CouplingMixture.diagonal baseLaw +
        ∑ i, ENNReal.ofReal (componentProbabilities κ m a b t i) •
          (rightLaw m a b i).prod (leftLaw m a b i) := by
    unfold pairLaw mixture
    rw [Measure.map_add _ _ measurable_swap, map_finsetSum _ _ measurable_swap]
    simp only [Measure.map_smul _ measurable_swap.aemeasurable, Measure.prod_swap]
    congr 1
    unfold CouplingMixture.diagonal
    rw [Measure.map_map measurable_swap (show Measurable (fun x : ℝ => (x, x)) from
      measurable_id.prodMk measurable_id)]
    rfl
  let d : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (diagonalMass κ m a b t) +
    ∑ i, ENNReal.ofReal (componentProbabilities κ m a b t i) *
      ENNReal.ofReal (rightDensity m a b i x)
  have hpair : (baseLaw.withDensity d) ⊗ₘ leftGivenRight κ m a b t =
      (pairLaw κ m a b t).map Prod.swap := by
    unfold leftGivenRight d
    rw [diagonalReplacementKernel_disintegration _ _ hq]
    · rw [hswap]
      unfold CouplingMixture.diagonal
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [rightLaw_eq_withDensity (by linarith) ha0 ha' hb0 hb']
    · exact finite_total _ _ _
  have hfst := congrArg Measure.fst hpair
  rw [Measure.fst_compProd, Measure.fst_map_swap] at hfst
  rw [← hfst]
  exact hpair

end SourceParameters
end Invariant233.OneCoordinateCoupling

end OAI
