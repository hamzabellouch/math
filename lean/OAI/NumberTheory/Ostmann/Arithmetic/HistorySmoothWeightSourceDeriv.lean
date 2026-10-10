import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightBinZero
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSourceLeaf

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicState.StateExpr
open Construction Characters.RationalHistory HistorySymbolicEncoding InitialCoordinatesTemplate
open scoped FourierTransform SchwartzMap
variable {ι : Type*} [DecidableEq ι] {a : State}

omit [DecidableEq ι] in
theorem sqrt_realPeriod_le_sourceRanges (e : StateExpr a ι) (b s k : ℕ)
    (X tb td G Δ E : ℝ) (center : ℕ → ℝ) (outside : List ℕ)
    (slot : ι → Option SmallSlot) (x : ι → ℝ)
    (hX : 0 < X) (hx : ∀ i, 0 < x i) (houtside : ∀ q ∈ outside, 0 < q)
    (hout : outside.length=2*s) (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (he : StateAtomSlots slot e) (hsource : IndependentSourceCells slot center x)
    (hp : 0 < e.plus.realEval x) (hm : 0 < e.minus.realEval x)
    (hgp : |Real.log (e.plus.realEval x)-G| ≤ 1)
    (hgm : |Real.log (e.minus.realEval x)-G| ≤ 1)
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑ h,∑ i,topCenters b center h i)+
      (∑ h,∑ j : Fin k,∑ i,compensationCenters b center h j i))
    (hbin : realStateBins b s tb td a outside (fun j => (e.small j).realEval x)
      (fun j => (outside.get j:ℝ)) ≠ 0) :
    Real.sqrt (X / e.realPeriod outside x) ≤ Real.exp ((-Δ+(E+12+4*(k:ℝ)))/2) := by
  have hsmall := StateAtomSlots.small_positive e he x hx
  have hcells := StateAtomSlots.small_cells e he center x hsource
  have hpos := expressionCoordinates_positive ha hout e x hp hm hsmall houtside
  have hlog := expressionCoordinates_log_support ha hout e x hpos G tb td
    (topCenters b center) (compensationCenters b center)
    (by intro h; cases h <;> assumption)
    (coordinates_top_cells ha hout _ _ _ _ center hcells)
    (coordinates_compensation_cells ha hout _ _ _ _ center hcells) hbin
  apply sqrt_ratio_le_of_log_lower X (e.realPeriod outside x) Δ (E+12+4*(k:ℝ)) hX
    (e.realPeriod_pos outside x hp hm hsmall houtside)
  have hh := (abs_le.mp hlog).1
  linarith

theorem realScalar_logCurve_deriv_le_sourceRanges (e : StateExpr a ι) (b s k : ℕ)
    (X tb td G Δ E K D : ℝ) (center : ℕ → ℝ) (outside : List ℕ)
    (slot : ι → Option SmallSlot) (x : ι → ℝ) (i : ι)
    (hX : 0 < X) (hx : ∀ j, 0 < x j) (houtside : ∀ q ∈ outside, 0 < q)
    (hout : outside.length=2*s) (ha : Template.Matches (Template.initial (2*b) k) a.small)
    (he : StateAtomSlots slot e) (hsource : IndependentSourceCells slot center x)
    (hp : 0 < e.plus.realEval x) (hm : 0 < e.minus.realEval x)
    (hgp : |Real.log (e.plus.realEval x)-G| ≤ 1)
    (hgm : |Real.log (e.minus.realEval x)-G| ≤ 1)
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑ h,∑ j,topCenters b center h j)+
      (∑ h,∑ j : Fin k,∑ r,compensationCenters b center h j r))
    (hK : 1 ≤ K) (hP : (e.periodExpr outside).RelativeControl x K)
    (hD : 0 ≤ D) (hφ : ∀ z, |deriv smoothPartition z| ≤ D) :
    ‖deriv (fun t => e.realScalar b s X tb td outside (Expr.logCurve x i t)) 0‖ ≤
      Real.exp ((-Δ+(E+12+4*(k:ℝ)))/2) *
        (leafProfileBound (𝓕 SchwartzCutoff.psi) * (e.periodExpr outside).logBudget K +
          leafFourierBound * (2*D*a.small.length)) := by
  have hsmall := StateAtomSlots.small_positive e he x hx
  have hpos := e.realPeriod_pos outside x hp hm hsmall houtside
  have hatoms : StateSmallAtoms e := fun j => by
    obtain ⟨r,hr,_⟩ := he j
    exact ⟨r,hr⟩
  have hfactor : 0 ≤ leafProfileBound (𝓕 SchwartzCutoff.psi) * (e.periodExpr outside).logBudget K +
      leafFourierBound * (2*D*a.small.length) := by
    exact add_nonneg (mul_nonneg (leafProfileBound_pos _).le (Expr.logBudget_nonneg _ (zero_le_one.trans hK)))
      (mul_nonneg leafFourierBound_pos.le (mul_nonneg (mul_nonneg (by norm_num) hD) (Nat.cast_nonneg _)))
  by_cases hbin : realStateBins b s tb td a outside (fun j => (e.small j).realEval x)
      (fun j => (outside.get j:ℝ)) = 0
  · rw [e.realScalar_logCurve_deriv_zero_of_bins_zero b s X tb td outside x i hX hx houtside
      hpos (Expr.RelativeControl.regular _ x K hP) hatoms hbin,norm_zero]
    exact mul_nonneg (Real.exp_pos _).le hfactor
  · exact (e.realScalar_logCurve_deriv_bound b s X tb td outside x i K D hX hx houtside hpos hK
      hP hatoms hD hφ).trans (mul_le_mul_of_nonneg_right
        (e.sqrt_realPeriod_le_sourceRanges b s k X tb td G Δ E center outside slot x hX hx houtside
          hout ha he hsource hp hm hgp hgm hcenter hbin) hfactor)

end Ostmann.Arithmetic.HistorySymbolicState.StateExpr

end

end OAI
