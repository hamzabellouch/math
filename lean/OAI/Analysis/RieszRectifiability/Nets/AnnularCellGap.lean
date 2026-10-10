import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.AnnularCellPairMasses
import OAI.Analysis.RieszRectifiability.Foundations.SmoothAnnularGapWitness

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def annularCellComparisonError (n : ℕ) (C G : ℝ) (D : ℝ≥0) : ℝ :=
  3 * ((D : ℝ) ^ 2 * (G * 2 ^ n * annularCellMassConstant n C) + 1) +
    3 * exteriorCellMeanConstant n G 1

theorem annularCellComparisonError_pos (n : ℕ) (C G : ℝ) (D : ℝ≥0)
    (hC : 0 < C) (hG : 0 ≤ G) : 0 < annularCellComparisonError n C G D := by
  have hmass := annularCellMassConstant_pos n C hC
  have hkernel := vectorKernelFarConstant_pos n
  unfold annularCellComparisonError exteriorCellMeanConstant
  positivity

theorem exists_annular_cell_gap {n d : ℕ} (hn : 1 ≤ n)
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R₀ k / 8))
    (a : Ambient d) (ha : a ∈ μ.support) (hnear : dist a (z : Ambient d) ≤ latticeRadius R₀ k / 8)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hRtop : R ≤ latticeRadius R₀ k / 8)
    (I : ℕ) (hdepth : annularLatticeDepth R₀ k r hr ≤ I)
    (S : Set (Ambient d)) (hS : MeasurableSet S) (hSfin : μ S < ∞) (hcontains : ball a (2 * R) ⊆ S)
    (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated n μ ε f) 2 μ ∧
        eLpNorm (truncated n μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) :
    ∃ (P : CellHaarPair μ R₀ hR₀ k z I) (e : Ambient d), ‖e‖ ≤ 1 ∧
      ∀ ε : ℝ, 0 < ε → ε < r / 2 →
        ‖smoothAnnularTransform n μ a r R hr (hr.trans_le hrR)‖ - annularCellComparisonError n C G D ≤
        |cellMean (μ.restrict P.innerCell) (fun x => inner ℝ e
            (truncated n μ ε (S.indicator (fun _ => 1)) x)) -
          cellMean (μ.restrict P.outerCell) (fun x => inner ℝ e
            (truncated n μ ε (S.indicator (fun _ => 1)) x))| := by
  obtain ⟨P, hPi, hPo, hmi, hmo⟩ := exists_annular_cell_pair_with_masses μ C G hC hG hg hlower
    R₀ hR₀ k z hcore a ha hnear r R hr hrR hRtop I hdepth
  have hfin := P.cells_finite G hg
  obtain ⟨e, he, hgap⟩ := exists_uniform_smooth_annular_gap_direction n hn G
    (annularCellMassConstant n C) μ hg a r R hr hrR S hS hSfin hcontains
    P.innerCell P.outerCell P.inner_measurable P.outer_measurable hfin.1 hfin.2
    (P.inner_real_pos C G hC hG hg hlower hcore) (P.outer_real_pos C G hC hG hg hlower hcore)
    hPi hPo hmi hmo D hRiesz
  exact ⟨P, e, he, hgap⟩

end

end RieszRectifiability

end OAI
