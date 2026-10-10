import OAI.Analysis.LipschitzHilbert.Phase.AngularErrorFamily

namespace OAI

/-! Reference-line moments for the actual angular-error coefficient sum,
with the manuscript's logarithmic dyadic source budget. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert
namespace AngularErrorFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem sources_log_budget (P : AngularErrorFamily N κ ι) (y : ℝ) :
    (P.sources y).sumBound =
      (P.sourceAmplitude * ((P.wideExponent+1 : ℕ)+4*P.smallRatio+
        (4/Real.log 2)*Real.log ((2:ℝ)^P.exponent))) * Real.pi :=
  actualErrorSources_log_sumBound P.wideExponent P.exponent P.direction P.direction_measurable
    P.referenceSlope P.angleBase P.smallRatio P.wideConstant P.sourceAmplitude P.topLength P.width y
    P.angleBase_pos P.smallRatio_pos P.sourceAmplitude_nonneg P.wideConstant_le P.topLength_pos P.width_pos

theorem error_moment (P : AngularErrorFamily N κ ι) (y : ℝ) (grid : FiniteLineGrid)
    (hb : 1 < grid.branching) (hwidth : P.topLength ≤ grid.width) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, (ENNReal.ofReal (P.error y x))^p ∂grid.lineMeasure) ≤
      (2:ℝ≥0∞)^p *
        (7 * ENNReal.ofReal ((p * (((grid.branching:ℝ)+2) *
          (2*(P.sources y).meanConstant+(P.sources y).oscillationConstant+1)) / Real.log (3/2))^p) +
          (ENNReal.ofReal (P.sources y).meanConstant)^p) * grid.lineMeasure Set.univ :=
  (P.sources y).dominated_error_moment grid hb hwidth (P.error y) (P.error_le_majorant y) hp

end AngularErrorFamily
end LipschitzHilbert

end

end OAI
