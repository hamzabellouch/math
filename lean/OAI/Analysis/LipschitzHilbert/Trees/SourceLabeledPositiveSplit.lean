import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledSynthesisEnvelope
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledCoefficientSplit

namespace OAI

/-! The actual source coefficient supplies the positive per-length
main/error bound for every residual subset, with original synthesis waves. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def physicalErrorScale (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (y x : ℝ) : ℝ :=
  ∑ l : P.labels j, ∑ u : Item j l, ‖P.physicalAngularErrorCoefficient t a b v g j l u‖*
    tileEnvelope (P.length j*(P.snappedSite j l u).1)
      (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y)

def physicalMainScale (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (y x : ℝ) : ℝ :=
  ∑ l : P.labels j, ∑ u : Item j l,
    ‖P.physicalFrozenCenteredCoefficient t a b v g j l u‖*P.positiveEnvelope j l u y x

theorem physicalErrorScale_nonneg (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (y x : ℝ) :
    0 ≤ P.physicalErrorScale t a b v g j y x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (norm_nonneg _) (tileEnvelope_nonneg _ _ _ _ _ _)

theorem physicalMainScale_nonneg (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (y x : ℝ) :
    0 ≤ P.physicalMainScale t a b v g j y x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (norm_nonneg _) (P.positiveEnvelope_nonneg _ _ _ _ _)

theorem sum_physicalErrorScale (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y x : ℝ) :
    (∑ j, P.physicalErrorScale t a b v g j y x) =
      P.physicalAngularError t a b v g (x,y+t*x) := by
  unfold physicalErrorScale physicalAngularError
  congr 1
  funext j
  have hy : y+t*x-t*x = y := by ring
  simp only [hy]

theorem actual_packet_subset_envelope (horder : 6 ≤ P.order) (i : Fin 3) (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (Q : Finset (Σ l : P.labels j, Item j l)) (y x : ℝ) :
    (∑ q ∈ Q, ‖P.rawPacketValue i j q.1 q.2
      (P.physicalMultiplierCoefficient t b v g j q.1 q.2) y x‖) ≤
        P.absoluteConstant*(P.physicalErrorScale t a b v g j y x+
          P.physicalMainScale t a b v g j y x) :=
  P.sum_raw_packet_values_split horder i j
    (P.physicalMultiplierCoefficient t b v g j)
    (P.physicalFrozenCenteredCoefficient t a b v g j)
    (P.physicalAngularErrorCoefficient t a b v g j)
    (fun l u => P.physicalMultiplierCoefficient_split t a b hb hb1 v hv g hg hg1 j l u) Q y x

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
