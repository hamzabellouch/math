import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.MarkedChild

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem markedFailure_le_one (p : PMF (Bool × Bool)) : markedFailure p ≤ 1 := by
  rw [← pmfMean_const p 1]
  apply pmfMean_mono
  intro z _
  split <;> norm_num

def ChargesCovered (charge : MarkedChild → Bool) (as : List MarkedChild) : Prop :=
  ∀ pre a post, as = pre ++ a :: post →
    a.required = false → charge a = true → markedDemand post = true

noncomputable def chargedFactor (charge : MarkedChild → Bool) (a : MarkedChild) : ℝ :=
  if a.required then markedGood a.law else if charge a then markedFailure a.law else 1

theorem chargedFactor_nonneg (c : MarkedChild → Bool) (a : MarkedChild) :
    0 ≤ chargedFactor c a := by
  unfold chargedFactor
  split
  · exact markedGood_nonneg _
  · split
    · exact markedFailure_nonneg _
    · exact zero_le_one

theorem markedBound_le_charged (charge : MarkedChild → Bool) (as : List MarkedChild)
    (hc : ChargesCovered charge as) :
    markedBound as ≤ (as.map (chargedFactor charge)).prod := by
  induction as with
  | nil => exact le_refl _
  | cons a as ih =>
    have hc' : ChargesCovered charge as := by
      intro pre b post hh hb hch
      apply hc (a :: pre) b post
      · simp only [List.cons_append, hh]
      · exact hb
      · exact hch
    have hpoint :
        (if a.required then markedGood a.law
          else if markedDemand as then markedFailure a.law else 1) ≤
        chargedFactor charge a := by
      by_cases hr : a.required = true
      · simp [chargedFactor, hr]
      · have hr' : a.required = false := Bool.eq_false_iff.mpr hr
        by_cases hq : charge a = true
        · have hd := hc [] a as rfl hr' hq
          simp [chargedFactor, hr', hq, hd]
        · simp only [chargedFactor, hr', Bool.false_eq_true, ↓reduceIte, hq]
          split
          · exact markedFailure_le_one _
          · exact le_refl _
    change _ * _ ≤ _ * _
    exact mul_le_mul hpoint (ih hc') (markedBound_nonneg as) (chargedFactor_nonneg _ _)

theorem marked_visitation_charged (charge : MarkedChild → Bool) (as : List MarkedChild)
    (hc : ChargesCovered charge as) :
    markedGood (markedCheck as) ≤ (as.map (chargedFactor charge)).prod :=
  (marked_visitation_bound as).trans (markedBound_le_charged charge as hc)

end SharpTerminalLeave

end

end OAI
