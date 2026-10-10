import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.SupportCellRoot
import OAI.Analysis.RieszRectifiability.Nets.CellBadCountBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem SupportCellDescendant.compose_injective {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (q : SupportCellDescendant μ R hR k z) : Function.Injective q.compose := by
  intro i j hij
  have hdepth : i.depth = j.depth := by
    have h := congrArg SupportCellDescendant.depth hij
    change q.depth + i.depth = q.depth + j.depth at h
    omega
  have hcell := congrArg SupportCellDescendant.cell hij
  rw [SupportCellDescendant.compose_cell, SupportCellDescendant.compose_cell] at hcell
  exact i.eq_of_common_point_same_depth j hdepth i.center i.center_mem_cell
    (hcell ▸ i.center_mem_cell)

theorem cellBadCountBound_rebase {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
    {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (N : ℕ) (x : Ambient d)
    (hcount : cellBadCountBound Bad q N x) :
    cellBadCountBound (fun i => Bad (q.compose i))
      (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩) N x := by
  classical
  intro F hF
  let e : SupportCellDescendant μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩ ↪
      SupportCellDescendant μ R hR k z := ⟨q.compose, q.compose_injective⟩
  have h := hcount (F.map e) (by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    have hiF := hF i hi
    refine ⟨hiF.1, ?_, ?_, ?_⟩
    · change q.depth ≤ q.depth + i.depth
      omega
    · change (q.compose i).cell ⊆ q.cell
      rw [SupportCellDescendant.compose_cell]
      exact i.cell_subset_top
    · change x ∈ (q.compose i).cell
      rw [SupportCellDescendant.compose_cell]
      exact hiF.2.2.2)
  simpa only [Finset.card_map] using! h

theorem beta_cellBadCountBound_rebase {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (H ε : ℝ)
    (q : SupportCellDescendant μ R hR k z) (N : ℕ) (x : Ambient d)
    (hcount : cellBadCountBound (fun i => ε ≤ bilateralBeta n μ i.center (H * i.radius)) q N x) :
    cellBadCountBound (fun i => ε ≤ bilateralBeta n μ i.center (H * i.radius))
      (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩) N x := by
  have h := cellBadCountBound_rebase
    (fun i => ε ≤ bilateralBeta n μ i.center (H * i.radius)) q N x hcount
  change cellBadCountBound (fun i => ε ≤ bilateralBeta n μ i.center (H * (q.compose i).radius))
    (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩) N x at h
  simpa only [SupportCellDescendant.compose_radius] using! h

end

end RieszRectifiability

end OAI
