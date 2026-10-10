import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledErrorTail
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledGoodQuantities

namespace OAI

/-! Natural moments of the actual labeled positive error on arbitrary
binary intervals. The constant depends on the source size and logarithmic
source sum, never on the number of available slope labels. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

def selectorErrorMomentBase (B : ℝ) : ℝ :=
  16*((4*(2*((1024*Real.pi^2)*B)+(240*Real.pi)*B+1))/Real.log (3/2)+
    (1024*Real.pi^2)*B+1)

theorem selectorErrorMomentBase_pos {B : ℝ} (hB : 0 ≤ B) :
    0 < selectorErrorMomentBase B := by
  have : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  unfold selectorErrorMomentBase
  positivity

namespace LabeledAngularErrorFamily
variable {N : ℕ} {Λ : Fin N → Type} {κ : Type} {ι : ∀ j, Λ j → Type}
  [∀ j, Fintype (Λ j)] [Fintype κ] [∀ j b, Fintype (ι j b)]

theorem error_joint_continuous (P : LabeledAngularErrorFamily N Λ κ ι) :
    Continuous (fun z : ℝ×ℝ => P.error z.1 z.2) := by
  apply continuous_finsetSum
  intro j _
  apply continuous_finsetSum
  intro b _
  apply continuous_finsetSum
  intro i _
  apply Continuous.mul continuous_const
  exact ((lineEnvelope_continuous _ _ _).comp continuous_snd).mul
    ((lineEnvelope_continuous _ _ _).comp continuous_fst)

/-- Every source family has the same polynomial moment bound on every
binary interval longer than its retained scales. -/
theorem error_moment_uniform (P : LabeledAngularErrorFamily N Λ κ ι)
    (B : ℝ) (_hB : 0 ≤ B)
    (hs : ∀ y, (P.sources y).sourceBound ≤ B)
    (ht : ∀ y, (P.sources y).sumBound ≤ B)
    (grid : FiniteLineGrid) (hg : grid.branching = 2)
    (hshort : ∀ j b (_u : ι j b), P.length j ≤ grid.width)
    (y : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (∫⁻ x, (ENNReal.ofReal (P.error y x))^n ∂grid.lineMeasure) ≤
      (ENNReal.ofReal (selectorErrorMomentBase B*(n:ℝ)))^n*grid.lineMeasure univ := by
  let Q := (P.sources y).restrictLength grid.width
  have hbase : Q.momentBase grid ≤ selectorErrorMomentBase B := by
    have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
    have hQs : Q.sourceBound ≤ B := hs y
    have hQt : Q.sumBound ≤ B := ht y
    unfold LineErrorSources.momentBase LineErrorSources.meanConstant
      LineErrorSources.oscillationConstant selectorErrorMomentBase
    rw [hg]
    norm_num only [Nat.cast_ofNat]
    gcongr
  have hm := Q.majorant_moment_natural grid (by omega)
    ((P.sources y).restrictLength_source_zero grid.width) n hn
  have hdom : (∫⁻ x, (ENNReal.ofReal (P.error y x))^n ∂grid.lineMeasure) ≤
      (∫⁻ x, (ENNReal.ofReal (Q.majorant x))^n ∂grid.lineMeasure) :=
    lintegral_mono fun x => pow_le_pow_left' (ENNReal.ofReal_le_ofReal
      (P.error_le_restricted_majorant grid.width hshort y x)) n
  apply hdom.trans (hm.trans _)
  rw [ENNReal.ofReal_pow (mul_nonneg (Q.momentBase_pos grid).le (Nat.cast_nonneg n))]
  exact mul_le_mul' (pow_le_pow_left' (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hbase (Nat.cast_nonneg n))) n) le_rfl

end LabeledAngularErrorFamily
end LipschitzHilbert

end

end OAI
