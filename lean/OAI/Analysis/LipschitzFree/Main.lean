import OAI.Analysis.LipschitzFree.BlockBAP
import OAI.Analysis.LipschitzFree.WedgeApproximation

namespace OAI

/-!
# A countable separated free space with AP and no finite BAP constant
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MainConstruction
open scoped Classical

instance radius_fact (n : ℕ) : Fact (0 < BlockParameters.R (n+1)) :=
  ⟨BlockParameters.R_pos (by omega)⟩

abbrev Piece (n : ℕ) := BlockConstruction.Block (n+1)
def pieceBase (n : ℕ) : Piece n := BlockConstruction.base (n+1)
abbrev Space := MetricWedge.Point Piece pieceBase
def base : Space := MetricWedge.base Piece pieceBase

theorem component_separated (n : ℕ) (x y : Piece n) (h : x ≠ y) : 1 ≤ dist x y :=
  BlockConstruction.separation (n+1) x y h

theorem separated (x y : Space) (h : x ≠ y) : 1 ≤ dist x y :=
  MetricWedge.separated Piece pieceBase component_separated x y h

theorem unbounded : ¬ Bornology.IsBounded (Set.univ : Set Space) := by
  intro h
  obtain ⟨r,hr⟩ := (Metric.isBounded_iff_subset_ball base).mp h
  obtain ⟨n,hn⟩ := exists_nat_gt r
  let x := MetricBlock.ofVertex (BlockConstruction.graph (n+1)) (BlockConstruction.color (n+1))
    (BlockParameters.D (n+1)) (BlockParameters.R (n+1)) (BlockConstruction.baseVertex (n+1))
  have hdist : dist (MetricWedge.inclusion Piece pieceBase n x) base = dist x (pieceBase n) := by
    rw [show base = MetricWedge.inclusion Piece pieceBase n (pieceBase n) from (MetricWedge.inclusion_base Piece pieceBase n).symm]
    exact (MetricWedge.inclusion_isometry Piece pieceBase n).dist_eq _ _
  have hu : dist (MetricWedge.inclusion Piece pieceBase n x) base < r := hr (Set.mem_univ _)
  rw [hdist] at hu
  have hl := BlockConstruction.original_radius (n+1) (by omega) (BlockConstruction.baseVertex (n+1))
  have hR : (n : ℝ) ≤ (BlockParameters.R (n+1) : ℝ) := by
    exact_mod_cast (show n ≤ BlockParameters.R (n+1) by
      dsimp [BlockParameters.R,BlockParameters.L]
      omega)
  change (BlockParameters.R (n+1) : ℝ) ≤ dist x (pieceBase n) at hl
  linarith

theorem nonproper : ¬ ProperSpace Space := by
  intro h
  let : ProperSpace Space := h
  let : DiscreteTopology Space := MetricWedge.discrete Piece pieceBase component_separated
  have hfin := (isCompact_closedBall base (BlockParameters.B 1 : ℝ)).finite_of_discrete
  have hs : Set.range (MetricWedge.inclusion Piece pieceBase 0) ⊆
      Metric.closedBall base (BlockParameters.B 1 : ℝ) := by
    rintro y ⟨x,rfl⟩
    change dist (MetricWedge.inclusion Piece pieceBase 0 x) base ≤ (BlockParameters.B 1 : ℝ)
    rw [show base = MetricWedge.inclusion Piece pieceBase 0 (pieceBase 0) from (MetricWedge.inclusion_base Piece pieceBase 0).symm]
    rw [(MetricWedge.inclusion_isometry Piece pieceBase 0).dist_eq]
    exact BlockConstruction.diameter 1 x (pieceBase 0)
  exact (Set.infinite_range_of_injective (MetricWedge.inclusion_isometry Piece pieceBase 0).injective) (hfin.subset hs)

theorem hasAP : HasAP (FreeSpace base) :=
  MetricWedge.hasAP Piece pieceBase component_separated
    (fun n => (BlockParameters.B (n+1) : ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun n x => BlockConstruction.diameter (n+1) x (pieceBase n))

theorem noBAP (Λ : ℝ) : ¬ HasBAP (FreeSpace base) Λ := by
  intro h
  obtain ⟨n,hn⟩ := exists_nat_ge Λ
  have hblock := hasBAP_of_contractive_retract (MetricWedge.inclusionL Piece pieceBase n)
    (MetricWedge.retractionL Piece pieceBase n) (MetricWedge.inclusionL_bound Piece pieceBase n)
    (MetricWedge.retractionL_bound Piece pieceBase n) (MetricWedge.retractionL_inclusionL Piece pieceBase n) Λ h
  exact BlockConstruction.noBAP (n+1) (by omega) Λ
    (by exact hn.trans (by exact_mod_cast Nat.le_succ n)) hblock

end DiscreteFree.MainConstruction

namespace DiscreteFree

theorem main_proved : MainStatement :=
  ⟨MainConstruction.Space,inferInstance,MainConstruction.base,inferInstance,
    MainConstruction.separated,MainConstruction.unbounded,MainConstruction.nonproper,
    MainConstruction.hasAP,fun Λ _ => MainConstruction.noBAP Λ⟩

end DiscreteFree
end

namespace DiscreteFree

theorem source_endpoints : BlockStatement ∧ MainStatement := ⟨blocks_proved, main_proved⟩

end DiscreteFree

end

end OAI
