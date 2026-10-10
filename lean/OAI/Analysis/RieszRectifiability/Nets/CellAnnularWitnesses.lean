import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.AnnularCellGap

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

structure CellAnnulus {d : ℕ} (μ : Measure (Ambient d)) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points) (ρ : ℝ) where
  center : Ambient d
  center_mem : center ∈ μ.support
  center_dist : dist center (z : Ambient d) ≤ latticeRadius R₀ k / 8
  innerRadius : ℝ
  outerRadius : ℝ
  inner_pos : 0 < innerRadius
  inner_le_outer : innerRadius ≤ outerRadius
  inner_lower : ρ * latticeRadius R₀ k ≤ innerRadius
  outer_upper : outerRadius ≤ latticeRadius R₀ k / 8

def CellAnnulus.transform {d : ℕ} {μ : Measure (Ambient d)} {R₀ : ℝ} {hR₀ : 0 < R₀}
    {k : ℕ} {z : (supportLatticeNets μ R₀ hR₀ k).points} {ρ : ℝ}
    (W : CellAnnulus μ R₀ hR₀ k z ρ) (n : ℕ) : Ambient d :=
  smoothAnnularTransform n μ W.center W.innerRadius W.outerRadius
    W.inner_pos (W.inner_pos.trans_le W.inner_le_outer)

def HasLargeCellAnnulus {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points) (ρ β : ℝ) : Prop :=
  ∃ W : CellAnnulus μ R₀ hR₀ k z ρ, β ≤ ‖W.transform n‖

theorem CellAnnulus.top_ball_contains {d : ℕ} {μ : Measure (Ambient d)}
    {R₀ : ℝ} {hR₀ : 0 < R₀} {k : ℕ} {z : (supportLatticeNets μ R₀ hR₀ k).points} {ρ : ℝ}
    (i : SupportCellDescendant μ R₀ hR₀ k z)
    (W : CellAnnulus μ R₀ hR₀ (k + i.depth) ⟨i.center, i.mem_net⟩ ρ) :
    ball W.center (2 * W.outerRadius) ⊆ ball (z : Ambient d) (4 * latticeRadius R₀ k) := by
  intro x hx
  have hxW : dist x W.center < 2 * W.outerRadius := hx
  have hW : dist W.center i.center ≤ i.radius / 8 := W.center_dist
  have hR : W.outerRadius ≤ i.radius / 8 := W.outer_upper
  have hi := i.center_dist_top
  have hr : i.radius ≤ latticeRadius R₀ k := latticeRadius_antitone R₀ hR₀.le (by omega)
  have ht1 := dist_triangle x W.center i.center
  have ht2 := dist_triangle x i.center (z : Ambient d)
  have hp := latticeRadius_pos R₀ hR₀ k
  change dist x (z : Ambient d) < 4 * latticeRadius R₀ k
  linarith

def CellHaarPair.refl {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) (I : ℕ) : CellHaarPair μ R hR k z I where
  outerOffset := 0
  innerOffset := 0
  depth_bound := Nat.zero_le I
  outerCenter := z
  innerCenter := z
  outer_ancestor := by apply Subtype.ext; rfl
  inner_ancestor := by apply Subtype.ext; rfl

theorem exists_uniform_depth_for_cell_annuli (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ I : ℕ, 0 < I ∧ ∀ (d : ℕ) (μ : Measure (Ambient d)) (R₀ : ℝ) (hR₀ : 0 < R₀)
      (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points) (W : CellAnnulus μ R₀ hR₀ k z ρ),
      annularLatticeDepth R₀ k W.innerRadius W.inner_pos ≤ I := by
  obtain ⟨I, hI, hb⟩ := exists_uniform_annular_lattice_depth ρ hρ
  exact ⟨I, hI, fun _ _ R₀ hR₀ k _ W => hb R₀ hR₀ k W.innerRadius W.inner_pos W.inner_lower⟩

end

end RieszRectifiability

end OAI
