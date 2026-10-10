import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledPositiveSplit
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedCoefficient
import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualSquare

namespace OAI

/-! A block's original packet set is restricted to each length before
using the fixed positive reference family. The bound is independent of
which path or mass cutoff selected the block. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem sum_sigma_fiber {I : Type*} [Fintype I] {U : I → Type*}
    [∀ j, Fintype (U j)] (f : (Σ j, U j) → ℝ) (j : I) :
    (∑ q ∈ Finset.univ.filter (fun q : Σ j, U j => q.1 = j), f q) =
      ∑ u : U j, f ⟨j,u⟩ := by
  classical
  rw [Finset.sum_filter,Fintype.sum_sigma,Finset.sum_eq_single j]
  · simp only [ite_true]
  · intro k _ hkj
    simp only [hkj,ite_false,Finset.sum_const_zero]
  · simp

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def physicalPacketValue (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (i : Fin 3) (z : ℝ×ℝ) (q : P.PacketIndex) : EuclideanSpace ℂ κ :=
  P.rawPacketValue i q.1 q.2.1 q.2.2
    (P.physicalMultiplierCoefficient t b v g q.1 q.2.1 q.2.2) (z.2-t*z.1) z.1

theorem physicalPacketValue_length_envelope (horder : 6 ≤ P.order) (i : Fin 3) (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (Q : Finset P.PacketIndex) (j : Fin N) (z : ℝ×ℝ) :
    (∑ q ∈ Q.filter (fun q => q.1 = j), ‖P.physicalPacketValue t b v g i z q‖) ≤
      P.absoluteConstant*(P.physicalErrorScale t a b v g j (z.2-t*z.1) z.1+
        P.physicalMainScale t a b v g j (z.2-t*z.1) z.1) := by
  classical
  calc
    _ ≤ ∑ q ∈ Finset.univ.filter (fun q : P.PacketIndex => q.1 = j),
        ‖P.physicalPacketValue t b v g i z q‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset_filter _ (Finset.subset_univ Q)) (fun _ _ _ => norm_nonneg _)
    _ = ∑ u : (Σ l : P.labels j, Item j l),
        ‖P.physicalPacketValue t b v g i z ⟨j,u⟩‖ := by
      rw [Finset.sum_filter,Fintype.sum_sigma,Finset.sum_eq_single j]
      · simp only [ite_true]
      · intro k _ hkj
        simp only [hkj,ite_false,Finset.sum_const_zero]
      · simp
    _ ≤ _ := P.actual_packet_subset_envelope horder i t a b hb hb1 v hv g hg hg1
      j Finset.univ (z.2-t*z.1) z.1

/-- The actual source residual square now follows from the original
coefficient split and packet geometry; no residual-envelope premise remains. -/
theorem physical_packet_residual_square_sum {τ : Type*}
    (horder : 6 ≤ P.order) (i : Fin 3) (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (hf : Measurable f) (hf1 : ∀ z, ‖f z‖ ≤ 1)
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → ℝ×ℝ → ℝ)
    (hp : ∀ T ∈ tops, 0 ≤ precision T) (hw : ∀ T z, 0 < weight T z)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (hz : ∀ k, 0 ≤ (phase k).re) (alpha : ℝ) (ha : 0 ≤ alpha) (z : ℝ×ℝ)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (stop : Fin N → ℕ) (mask : τ → ℂ)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (he : ∀ q ∈ packets, grid.eligible cutoff (precision (assigned q)) (stop q.1))
    (C : ℝ) (hC : 0 ≤ C) (hmask : ∀ T ∈ tops, weight T z^(-alpha)*‖mask T‖ ≤ C)
    (level : ℕ → ℕ) (hlevel : StrictMono level) (count : ℕ) (pathSlope : ℝ)
    (R : ℝ) (hR : 0 ≤ R)
    (hcard : ∀ j < count,
      ((residualLengthSet stop (level j) (level (j+1))).card:ℝ) ≤ R) :
    let value := P.physicalPacketValue t b v f i z
    (∑ j : Fin count, ‖grid.packetResidual packets (fun q => slope (assigned q))
      (fun q => stop q.1)
      (grid.sourcePacketBase tops slope precision cutoff weight assigned (fun q => stop q.1)
        (fun q => mask (assigned q) • value q) alpha z)
      (grid.sourceTransition tops slope precision cutoff weight K gap phase z)
      (level j.val) (level (j.val+1)) (grid.index (level j.val) pathSlope)‖^2) ≤
        3*C^2*((∑ k, P.absoluteConstant*P.physicalErrorScale t a b v f k (z.2-t*z.1) z.1)^2+
          R*∑ k, (P.absoluteConstant*P.physicalMainScale t a b v f k (z.2-t*z.1) z.1)^2) := by
  classical
  dsimp only
  apply grid.source_packet_residual_square_sum tops slope precision cutoff weight hp hw hK gap
    phase hz alpha ha z packets assigned (fun q : P.PacketIndex => q.1) stop mask
    (P.physicalPacketValue t b v f i z) hassigned he C hC hmask level hlevel count pathSlope
    (fun k => P.absoluteConstant*P.physicalErrorScale t a b v f k (z.2-t*z.1) z.1)
    (fun k => P.absoluteConstant*P.physicalMainScale t a b v f k (z.2-t*z.1) z.1)
    (fun k => mul_nonneg P.absoluteConstant_pos.le (P.physicalErrorScale_nonneg t a b v f k _ _))
    (fun k => mul_nonneg P.absoluteConstant_pos.le (P.physicalMainScale_nonneg t a b v f k _ _))
    R hR hcard
  intro j _ k _
  have h := P.physicalPacketValue_length_envelope horder i t a b hb hb1 v hv f hf hf1
    ((grid.packetSet packets (fun q => slope (assigned q)) (fun q => stop q.1)
      (level j) (grid.index (level j) pathSlope)).filter (fun q => stop q.1 < level (j+1))) k z
  simpa only [mul_add] using h

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
