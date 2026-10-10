import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalReferenceSquare

namespace OAI

/-! A single physical centered main square is controlled by three
reference squares. The resulting exceptional-set inclusion is exact. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

def physicalCenteredSquare (s t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y x : ℝ) : ℝ :=
  Real.sqrt (∑ j, P.physicalCenteredPositiveScale s t d v g j y x^2)

 theorem physicalCenteredSquare_nonneg (s t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y x : ℝ) :
    0 ≤ P.physicalCenteredSquare s t d v g y x := Real.sqrt_nonneg _

 theorem physicalCenteredSquare_sq (s t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y x : ℝ) :
    (P.physicalCenteredSquare s t d v g y x)^2 =
      ∑ j, P.physicalCenteredPositiveScale s t d v g j y x^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

 theorem physicalCenteredSquare_continuous (s t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y : ℝ) :
    Continuous (P.physicalCenteredSquare s t d v g y) := by
  apply Continuous.sqrt
  apply continuous_finsetSum
  intro j _
  apply Continuous.pow
  apply continuous_finsetSum
  intro u _
  unfold positiveEnvelope lineEnvelope
  apply Continuous.mul continuous_const
  apply Continuous.mul _ continuous_const
  apply Continuous.inv₀
  · fun_prop
  · intro x
    positivity

 theorem physicalCenteredSquare_bad_subset (s t : ℝ) (d : Fin N → ℝ)
    (hd : ∀ j, 0 ≤ d j) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (y small large : ℝ) (hsmall : 0 < small)
    (hlarge : 4*(P.constant*Real.pi^2)*small ≤ large) :
    {x | large ≤ P.physicalCenteredSquare s t d v g y x} ⊆
      {x | small ≤ |P.physicalReferenceSquare s (fun j => t+d j) v hv g hg hg1 y x|} ∪
      {x | small ≤ |P.physicalReferenceSquare s (fun j => d j-t) (fun z => -v z) hv.neg g hg hg1 y x|} ∪
      {x | small ≤ |P.physicalReferenceSquare s (fun _ => 0) (fun _ => 0) measurable_const g hg hg1 y x|} := by
  intro x hx
  by_contra hn
  simp only [Set.mem_union,Set.mem_ofPred_eq,not_or] at hn
  have hU := lt_of_not_ge hn.1.1
  have hD := lt_of_not_ge hn.1.2
  have hT := lt_of_not_ge hn.2
  have hUsq : (P.physicalReferenceSquare s (fun j => t+d j) v hv g hg hg1 y x)^2 ≤ small^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hU.le 2
  have hDsq : (P.physicalReferenceSquare s (fun j => d j-t) (fun z => -v z) hv.neg g hg hg1 y x)^2 ≤ small^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hD.le 2
  have hTsq : (P.physicalReferenceSquare s (fun _ => 0) (fun _ => 0) measurable_const g hg hg1 y x)^2 ≤ small^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hT.le 2
  have hbound := P.physicalCenteredPositiveScale_square_reference t d v hv g hg hg1 s hd y x
  rw [← P.physicalCenteredSquare_sq s t d v g] at hbound
  have hC : 0 < P.constant*Real.pi^2 := mul_pos P.constant_pos (pow_pos Real.pi_pos _)
  have hCs : 0 < (P.constant*Real.pi^2)*small := mul_pos hC hsmall
  have hsum : (P.physicalCenteredSquare s t d v g y x)^2 ≤
      9*(P.constant*Real.pi^2)^2*small^2 := by
    have hscaled := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hUsq hDsq) hTsq)
      (by positivity : 0 ≤ 3*(P.constant*Real.pi^2)^2)
    nlinarith
  have h0 := P.physicalCenteredSquare_nonneg s t d v g y x
  have hpoint : P.physicalCenteredSquare s t d v g y x ≤ 3*(P.constant*Real.pi^2)*small := by
    nlinarith
  change large ≤ P.physicalCenteredSquare s t d v g y x at hx
  nlinarith

end LipschitzHilbert.SourceLatticePacket

end

end OAI
