import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSourceBasic
import OAI.NumberTheory.Ostmann.Construction.InitialCoordinatesTemplateCells

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
open Construction Characters.RationalHistory HistorySymbolicState HistorySymbolicEncoding
open InitialCoordinatesTemplate

def sourceLeafAmplitude (k : ℕ) (Δ E : ℝ) : ℝ :=
  leafFourierBound * Real.exp ((-Δ+(E+12+4*(k:ℝ)))/2)

theorem sourceLeafAmplitude_pos (k : ℕ) (Δ E : ℝ) : 0 < sourceLeafAmplitude k Δ E :=
  mul_pos leafFourierBound_pos (Real.exp_pos _)

theorem HistorySymbolicState.StateExpr.realScalar_norm_le_sourceRanges {ι : Type*} {a : State}
    (e : StateExpr a ι) (b s k : ℕ) (X tb td G Δ E : ℝ) (center : ℕ → ℝ)
    (outside : List ℕ) (slot : ι → Option SmallSlot) (x : ι → ℝ)
    (hX : 0 < X) (hx : ∀ i, 0 < x i) (houtside : ∀ q ∈ outside, 0 < q)
    (hout : outside.length = 2*s) (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (he : StateAtomSlots slot e) (hsource : IndependentSourceCells slot center x)
    (hp : 0 < e.plus.realEval x) (hm : 0 < e.minus.realEval x)
    (hgp : |Real.log (e.plus.realEval x)-G| ≤ 1)
    (hgm : |Real.log (e.minus.realEval x)-G| ≤ 1)
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑ h,∑ i,topCenters b center h i)+
      (∑ h,∑ j : Fin k,∑ i,compensationCenters b center h j i)) :
    ‖e.realScalar b s X tb td outside x‖ ≤ sourceLeafAmplitude k Δ E := by
  have hcells := StateAtomSlots.small_cells e he center x hsource
  have hpos := expressionCoordinates_positive ha hout e x hp hm
    (StateAtomSlots.small_positive e he x hx) houtside
  rw [← expressionCoordinates_scalar ha hout e x X tb td]
  apply realLeafScalar_norm_le_of_source_cells _ hpos X hX a.frequency G tb td Δ E
    (topCenters b center) (compensationCenters b center)
  · intro h
    cases h <;> assumption
  · exact coordinates_top_cells ha hout _ _ _ _ center hcells
  · exact coordinates_compensation_cells ha hout _ _ _ _ center hcells
  · exact hcenter

end Ostmann.Arithmetic

end

end OAI
