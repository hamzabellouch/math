import OAI.Combinatorics.BalancedRyser.Probability.FiniteFixedLaw
import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentModel

namespace OAI

namespace Balanced.ConditionalRestriction

noncomputable section
open scoped Classical
open MeasureTheory

universe u
variable {D A : Type u} [Fintype D] [Fintype A] [DecidableEq D] [Nonempty A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

private def uniformArrayModel : PatternModel.{u} where
  Color := D
  Value := fun _ => A
  law := fun _ => (PMF.uniformOfFintype A).toMeasure
  Label := PUnit
  support := fun _ => ∅
  event := fun _ => ∅
  eventMeasurable := fun _ => MeasurableSet.empty
  dependsOn := by intros; rfl

theorem filtered_integral_mul_le (old extra : Finset D) (a : D → A)
    (f z : (D → A) → ℝ) (C Bf Bz : ℝ) (hC : 0 ≤ C)
    (hfn : ∀ ω, 0 ≤ f ω) (hzn : ∀ ω, 0 ≤ z ω)
    (hfb : ∀ ω, f ω ≤ Bf) (hzb : ∀ ω, z ω ≤ Bz)
    (hdepends : ∀ ω ω', (∀ d ∈ old ∪ extra, ω d = ω' d) → f ω = f ω')
    (hbound : ∀ y : D → A,
      (∫ ω, z ω ∂((PMF.uniformOfFintype (D → A)).filter
        {ω | ∀ d, d ∈ old ∪ extra → ω d = y d}
        (fixed_supported (fun d => d ∈ old ∪ extra) y)).toMeasure) ≤ C) :
    (∫ ω, f ω * z ω ∂((PMF.uniformOfFintype (D → A)).filter
      {ω | ∀ d, d ∈ old → ω d = a d}
      (fixed_supported (fun d => d ∈ old) a)).toMeasure) ≤
      C * ∫ ω, f ω ∂((PMF.uniformOfFintype (D → A)).filter
        {ω | ∀ d, d ∈ old → ω d = a d}
        (fixed_supported (fun d => d ∈ old) a)).toMeasure := by
  let P : PatternModel := uniformArrayModel (D := D) (A := A)
  have hconvert (J : Finset D) (y : D → A) (G : (D → A) → ℝ) :
      P.fixedExpectation J y G =
        ∫ ω, G ω ∂((PMF.uniformOfFintype (D → A)).filter
          {ω | ∀ d, d ∈ J → ω d = y d}
          (fixed_supported (fun d => d ∈ J) y)).toMeasure := by
    rw [← integral_fixArray_eq_filtered (fun d => d ∈ J) y G]
    apply integral_congr_ae
    filter_upwards [] with ω
    congr 1
    funext d
    dsimp [P, uniformArrayModel, PatternModel.fixCoordinates, fixArray]
    exact @ite_cond_congr A (d ∈ J) (d ∈ J)
      (Finset.decidableMem d J) (Classical.propDecidable _) (y d) (ω d) rfl
  rw [← hconvert old a (fun ω => f ω * z ω), ← hconvert old a f]
  apply P.fixedExpectation_mul_le_of_fixedBounds old extra a f z C Bf Bz hC
    (show Measurable f from measurable_of_countable f)
    (show Measurable z from measurable_of_countable z) hfn hzn hfb hzb hdepends
  intro y
  exact (hconvert (old ∪ extra) y z).trans_le (hbound y)

theorem integral_eq_of_eq_on_support {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (f g : Ω → ℝ) (h : ∀ ω ∈ p.support, f ω = g ω) :
    (∫ ω, f ω ∂p.toMeasure) = ∫ ω, g ω ∂p.toMeasure := by
  simp only [PMF.integral_eq_sum, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : ω ∈ p.support
  · rw [h ω hω]
  · have hp : p ω = 0 := by simpa [PMF.mem_support_iff] using hω
    simp [hp]

end
end Balanced.ConditionalRestriction

end OAI
