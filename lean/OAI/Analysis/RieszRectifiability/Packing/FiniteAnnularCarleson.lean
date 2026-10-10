import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.CellAnnularWitnesses
import OAI.Analysis.RieszRectifiability.Packing.HaarTopBallPacking
import OAI.Analysis.RieszRectifiability.Kernel.CommonFiniteTruncation

namespace OAI

/-!
# Finite annular witness packing

Annular witnesses with bounded lattice depth give Haar mean gaps at one common
positive truncation scale. Applying top-ball Haar packing to those gaps bounds
the total mass of the selected descendant cells by the original top-cell mass.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem finite_annular_witness_mass_packing {n d : ℕ} (hn : 1 ≤ n)
    (μ : Measure (Ambient d)) (C G ρ v : ℝ) (hC : 0 < C) (hG : 0 < G) (hv : 0 < v)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R₀ : ℝ) (hR₀ : 0 < R₀) (k I : ℕ) (hI : 0 < I)
    (z : (supportLatticeNets μ R₀ hR₀ k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R₀ k / 8))
    (s : Finset (SupportCellDescendant μ R₀ hR₀ k z))
    (W : (i : s) → CellAnnulus μ R₀ hR₀ (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩ ρ)
    (hdepth : ∀ i : s, annularLatticeDepth R₀ (k + i.val.depth) (W i).innerRadius (W i).inner_pos ≤ I)
    (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated n μ ε f) 2 μ ∧
        eLpNorm (truncated n μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (hlarge : ∀ i : s, annularCellComparisonError n C G D + v ≤ ‖(W i).transform n‖) :
    ∑ i ∈ s, μ.real i.cell ≤
      haarTopBallPackingConstant n C G 4 v D I * μ.real (cleanSupportCell μ R₀ hR₀ k z) := by
  classical
  let S := ball (z : Ambient d) (4 * latticeRadius R₀ k)
  have hSfin : μ S < ∞ := (hg.2 z _ (by have hp := latticeRadius_pos R₀ hR₀ k; positivity)).trans_lt
    ENNReal.ofReal_lt_top
  have hchoose (i : s) := exists_annular_cell_gap hn μ C G hC hG hg hlower R₀ hR₀
    (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩
    (lattice_core_admissible_at_later_level μ R₀ hR₀ k _ (by omega) hcore)
    (W i).center (W i).center_mem (W i).center_dist (W i).innerRadius (W i).outerRadius
    (W i).inner_pos (W i).inner_le_outer (W i).outer_upper I (hdepth i)
    S measurableSet_ball hSfin ((W i).top_ball_contains i.val) D hRiesz
  choose P e he hgap using hchoose
  obtain ⟨ε, hε, hsmall⟩ := exists_positive_below_finset (Finset.univ : Finset s)
    (fun i : s => (W i).innerRadius / 2) (fun i _ => half_pos (W i).inner_pos)
  let P' : (i : SupportCellDescendant μ R₀ hR₀ k z) →
      CellHaarPair μ R₀ hR₀ (k + i.depth) ⟨i.center, i.mem_net⟩ I := fun i =>
    if hi : i ∈ s then P ⟨i, hi⟩ else CellHaarPair.refl μ R₀ hR₀ (k + i.depth) ⟨i.center, i.mem_net⟩ I
  let e' : SupportCellDescendant μ R₀ hR₀ k z → Ambient d := fun i =>
    if hi : i ∈ s then e ⟨i, hi⟩ else 0
  have he' : ∀ i ∈ s, ‖e' i‖ ≤ 1 := by
    intro i hi
    simpa only [e', dite_eq_left hi] using! he ⟨i, hi⟩
  have hgap' : ∀ i ∈ s, v ≤
      |cellMean (μ.restrict (P' i).innerCell) (fun x => inner ℝ (e' i)
          (truncated n μ ε (topCellBallIndicator μ R₀ hR₀ k z 4) x)) -
        cellMean (μ.restrict (P' i).outerCell) (fun x => inner ℝ (e' i)
          (truncated n μ ε (topCellBallIndicator μ R₀ hR₀ k z 4) x))| := by
    intro i hi
    have hb := hgap ⟨i, hi⟩ ε hε (hsmall ⟨i, hi⟩ (Finset.mem_univ _))
    have hl := hlarge ⟨i, hi⟩
    change ‖(W ⟨i, hi⟩).transform n‖ - annularCellComparisonError n C G D ≤ _ at hb
    simp only [P', e', dite_eq_left hi, topCellBallIndicator]
    change v ≤ _
    dsimp only [S] at hb
    linarith
  exact bounded_depth_haar_top_ball_packing μ C G 4 hC hG (by norm_num) hg hlower
    R₀ hR₀ k I hI z hcore P' s D hRiesz ε hε e' he' v hv hgap'

end

end RieszRectifiability

end OAI
