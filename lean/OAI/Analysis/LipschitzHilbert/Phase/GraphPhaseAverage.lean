import OAI.Analysis.LipschitzHilbert.Geometry.LocalMinimaSelection
import OAI.Analysis.LipschitzHilbert.Phase.DiagonalPhaseSelection
import OAI.Analysis.LipschitzHilbert.Geometry.SeparatedPacking

namespace OAI

/-! Weighted prediction using the explicitly constructed independent-set law. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] [Fintype κ] in
theorem independent_card_le_span (G : ι → ι → Prop) (frequency : ι → ℝ)
    {gap a b : ℝ} (hgap : 0 < gap) (hab : a ≤ b)
    (hfrequency : ∀ i j, i ≠ j → ¬G i j → gap ≤ |frequency i - frequency j|)
    (hbound : ∀ i, a ≤ frequency i ∧ frequency i ≤ b)
    (S : Finset ι) (hS : (S : Set ι).Pairwise (fun i j => ¬G i j)) :
    (S.card : ℝ) ≤ 1 + (b - a) / gap := by
  classical
  have hsep : Separated (fun i : S => frequency i) gap := by
    intro i j hij
    have hij' : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    exact hfrequency i.val j.val hij' (hS i.property j.property hij')
  simpa only [Fintype.card_coe] using separated_card_le_span
    (fun i : S => frequency i) hgap hab hsep (fun i => hbound i)

theorem graph_weighted_diagonal_prediction_average
    (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i)
    (w m : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : ∀ i, orderMass w (closedNeighborhood G i) ≤ m i)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (frequency : ι → κ → ℝ)
    (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ) (lambda : ι → ℂ)
    {gap D p : ℝ} (hgap : 0 < gap) (hν : FourierGap ν gap) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hfrequency : ∀ i j, i ≠ j → ¬G i j → ∀ k, gap ≤ |frequency i k - frequency j k|)
    (hcard : ∀ S : Finset ι, (S : Set ι).Pairwise (fun i j => ¬G i j) → (S.card : ℝ) ≤ D)
    (hl : ∀ i, 0 ≤ l i) (htotal : ∑ i, l i ≤ 1)
    (hlambda : ∀ i, ‖lambda i‖ ≤ (w i / m i) ^ phaseMu D p) :
    (∫ t, (1 + ‖diagonalFourierSum frequency
      (fun i => (((l i ^ (1 - phaseMu D p) : ℝ) : ℂ) * lambda i) • X i) t‖ ^ p) /
      (1 + ∑ i, l i * ‖X i‖ ^ p) ∂ν) ≤ 1 := by
  classical
  let L := localMinimaLaw G hG w hw
  have hmass (i : ι) : 0 < m i := (orderMass_pos w _ (fun j _ => hw j)
    ⟨i, (mem_closedNeighborhood G i i).2 (Or.inl rfl)⟩).trans_le (hm i)
  apply weighted_diagonal_prediction_average_at_p L ν frequency l (fun i => w i / m i)
    X lambda hgap hν hD hp
  · intro ω _ k i j hij
    have hij' : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    exact hfrequency i.val j.val hij' (ω.property i.property j.property hij') k
  · intro ω _
    exact hcard ω.val ω.property
  · exact hl
  · exact htotal
  · intro i
    exact div_pos (hw i) (hmass i)
  · exact localMinimaLaw_marginal_lower G hG w hw m hm
  · exact hlambda

end LipschitzHilbert

end

end OAI
