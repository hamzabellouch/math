import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledRawEnvelope
import OAI.Analysis.LipschitzHilbert.Packets.PacketVectorDerivative

namespace OAI

/-! Pointwise norms of actual vector packets are controlled by the
same positive main and error envelopes used in the reference tails. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def positiveEnvelope (j : Fin N) (l : P.labels j) (u : Item j l) (y x : ℝ) : ℝ :=
  lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) 3 x*
    lineEnvelope (P.width*(P.snappedSite j l u).2) P.width 2 y

theorem positiveEnvelope_nonneg (j : Fin N) (l : P.labels j) (u : Item j l) (y x : ℝ) :
    0 ≤ P.positiveEnvelope j l u y x :=
  mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

theorem tileEnvelope_le_positive (j : Fin N) (l : P.labels j) (u : Item j l) (y x : ℝ) :
    tileEnvelope (P.length j*(P.snappedSite j l u).1)
      (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y) ≤
        P.positiveEnvelope j l u y x :=
  mul_le_mul (lineEnvelope_antitone _ _ _ (by decide : 3 ≤ 6))
    (lineEnvelope_antitone _ _ _ (by decide : 2 ≤ 6))
    (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

def rawPacketValue (i : Fin 3) (j : Fin N) (l : P.labels j) (u : Item j l)
    (c : EuclideanSpace ℂ κ) (y x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => c k*P.raw i j l u k y x)

theorem raw_packet_value_norm (horder : 6 ≤ P.order) (i : Fin 3) (j : Fin N)
    (l : P.labels j) (u : Item j l) (c : EuclideanSpace ℂ κ) (y x : ℝ) :
    ‖P.rawPacketValue i j l u c y x‖ ≤
      P.absoluteConstant*(‖c‖*tileEnvelope (P.length j*(P.snappedSite j l u).1)
        (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y)) := by
  have h := diagonal_packet_norm c (fun k => P.raw i j l u k y x)
    (mul_nonneg P.absoluteConstant_pos.le (tileEnvelope_nonneg _ _ _ _ _ _))
    (fun k => P.raw_absolute_tileEnvelope horder i j l u k (x,y))
  exact h.trans_eq (by ring)

theorem raw_packet_value_split (horder : 6 ≤ P.order) (i : Fin 3) (j : Fin N)
    (l : P.labels j) (u : Item j l) (c main error : EuclideanSpace ℂ κ)
    (hsplit : c = main+error) (y x : ℝ) :
    ‖P.rawPacketValue i j l u c y x‖ ≤
      P.absoluteConstant*(‖error‖*tileEnvelope
        (P.length j*(P.snappedSite j l u).1) (P.width*(P.snappedSite j l u).2)
        (P.length j) P.width 6 (x,y)+‖main‖*P.positiveEnvelope j l u y x) := by
  apply (P.raw_packet_value_norm horder i j l u c y x).trans
  apply mul_le_mul_of_nonneg_left _ P.absoluteConstant_pos.le
  have hc : ‖c‖ ≤ ‖main‖+‖error‖ :=
    hsplit ▸ norm_add_le _ _
  calc
    _ ≤ (‖main‖+‖error‖)*tileEnvelope _ _ _ _ 6 (x,y) :=
      mul_le_mul_of_nonneg_right hc (tileEnvelope_nonneg _ _ _ _ _ _)
    _ ≤ _ := by
      have he := mul_le_mul_of_nonneg_left (P.tileEnvelope_le_positive j l u y x)
        (norm_nonneg main)
      nlinarith

/-- Every path-dependent packet subset is bounded by the one fixed
positive reference family. -/
theorem sum_raw_packet_values_split (horder : 6 ≤ P.order) (i : Fin 3) (j : Fin N)
    (c main error : ∀ l : P.labels j, Item j l → EuclideanSpace ℂ κ)
    (hsplit : ∀ l u, c l u = main l u+error l u)
    (Q : Finset (Σ l : P.labels j, Item j l)) (y x : ℝ) :
    (∑ q ∈ Q, ‖P.rawPacketValue i j q.1 q.2 (c q.1 q.2) y x‖) ≤
      P.absoluteConstant*((∑ l : P.labels j, ∑ u : Item j l,
        ‖error l u‖*tileEnvelope (P.length j*(P.snappedSite j l u).1)
          (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 (x,y))+
        ∑ l : P.labels j, ∑ u : Item j l, ‖main l u‖*P.positiveEnvelope j l u y x) := by
  classical
  calc
    _ ≤ ∑ q : (Σ l : P.labels j, Item j l), ‖P.rawPacketValue i j q.1 q.2 (c q.1 q.2) y x‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Q) (fun _ _ _ => norm_nonneg _)
    _ ≤ ∑ q : (Σ l : P.labels j, Item j l), P.absoluteConstant*(‖error q.1 q.2‖*tileEnvelope
        (P.length j*(P.snappedSite j q.1 q.2).1) (P.width*(P.snappedSite j q.1 q.2).2)
        (P.length j) P.width 6 (x,y)+‖main q.1 q.2‖*P.positiveEnvelope j q.1 q.2 y x) :=
      by
        apply Finset.sum_le_sum
        intro q _
        have h := P.raw_packet_value_split horder i j q.1 q.2
          (c q.1 q.2) (main q.1 q.2) (error q.1 q.2) (hsplit q.1 q.2) y x
        exact h
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_add_distrib]; simp only [Fintype.sum_sigma]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
