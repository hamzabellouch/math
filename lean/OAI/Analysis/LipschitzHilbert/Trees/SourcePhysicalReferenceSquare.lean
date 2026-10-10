import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalPositiveScale

namespace OAI

/-! The physical positive main square is exactly the normalized
reference square function times its coefficient normalization. This
connects the symmetric frozen main term to three proved line estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

def physicalReferenceLine (t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (y : ℝ) : LinePacketFamily N κ ι :=
  P.referenceAnalyzedLine d (fun z => v (sourceReferenceToPhysical t z))
    (hv.comp (sourceReferenceToPhysical t).measurable)
    (fun z => g (sourceReferenceToPhysical t z))
    (hg.comp (sourceReferenceToPhysical t).measurable) (fun _ => hg1 _) y

def physicalReferenceSquare (t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (y x : ℝ) : ℝ :=
  (P.physicalReferenceLine t d v hv g hg hg1 y).squareFunction (x/P.topLength)

variable (t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

theorem physicalPositiveScale_eq_reference (j : Fin N) (y x : ℝ) :
    P.physicalPositiveScale t d v g j y x = (P.constant*Real.pi^2)*
      (P.physicalReferenceLine t d v hv g hg hg1 y).positiveScale j (x/P.topLength) := by
  have h := P.referenceAnalyzedLine_positiveScale d v hv g hg hg1 t y (x/P.topLength) j
  have hx : P.topLength*(x/P.topLength) = x := by field_simp [P.topLength_pos.ne']
  rw [hx] at h
  change _ = (P.constant*Real.pi^2)*_
  dsimp only [physicalReferenceLine]
  rw [h,← mul_assoc,mul_inv_cancel₀ (mul_pos P.constant_pos (pow_pos Real.pi_pos _)).ne',one_mul]

theorem physicalPositiveScale_square_sum_eq (y x : ℝ) :
    (∑ j, P.physicalPositiveScale t d v g j y x^2) =
      (P.constant*Real.pi^2)^2*(P.physicalReferenceSquare t d v hv g hg hg1 y x)^2 := by
  unfold physicalReferenceSquare LinePacketFamily.squareFunction
  rw [Real.sq_sqrt ((P.physicalReferenceLine t d v hv g hg hg1 y).squareSum_nonneg _)]
  unfold LinePacketFamily.squareSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [P.physicalPositiveScale_eq_reference t d v hv g hg hg1,mul_pow]

theorem physicalCenteredPositiveScale_square_reference (s : ℝ)
    (hd : ∀ j, 0 ≤ d j) (y x : ℝ) :
    (∑ j, P.physicalCenteredPositiveScale s t d v g j y x^2) ≤
      (3*(P.constant*Real.pi^2)^2)*
        ((P.physicalReferenceSquare s (fun j => t+d j) v hv g hg hg1 y x)^2+
         (P.physicalReferenceSquare s (fun j => d j-t) (fun z => -v z) hv.neg g hg hg1 y x)^2+
         (P.physicalReferenceSquare s (fun _ => 0) (fun _ => 0) measurable_const g hg hg1 y x)^2) := by
  have h := P.physicalCenteredPositiveScale_square_sum_le s t d hd v hv g hg hg1 y x
  rw [P.physicalPositiveScale_square_sum_eq s (fun j => t+d j) v hv g hg hg1,
    P.physicalPositiveScale_square_sum_eq s (fun j => d j-t) (fun z => -v z) hv.neg g hg hg1,
    P.physicalPositiveScale_square_sum_eq s (fun _ => 0) (fun _ => 0) measurable_const g hg hg1] at h
  convert h using 1
  ring

end LipschitzHilbert.SourceLatticePacket

end

end OAI
