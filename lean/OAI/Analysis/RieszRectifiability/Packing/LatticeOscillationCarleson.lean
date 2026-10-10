import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.LatticeMassPacking
import OAI.Analysis.RieszRectifiability.Nets.BadCellTestFamily
import OAI.Analysis.RieszRectifiability.Packing.RieszOscillationPacking

namespace OAI

/-!
# Carleson packing of bad lattice descendants

Riesz oscillation packing bounds the radii of bad support descendants. The
lattice mass comparison converts this into a mass packing estimate, with a
positive constant uniform over measures satisfying the growth and Riesz bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem bad_support_descendants_radius_packing {p d : ℕ} [Nontrivial (Ambient d)]
    (μ : Measure (Ambient d)) [SFinite μ] (C G J v : ℝ)
    (hC : 0 < C) (hJ : 0 < J) (hv : 0 < v) (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r))
    (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated (p + 1) μ ε f) 2 μ ∧
        eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (N : ℕ) (hN : (1 / 2 : ℝ) ^ N ≤ smallRieszRadiusFraction (p + 1) G J v)
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (s : Finset (BadSupportDescendant (p + 1) μ R hR k z J v)) :
    ∑ i ∈ s, i.val.radius ^ (p + 1) ≤
      rieszOscillationPackingConstant (p + 1) C G (1 / 8) J v D N *
        (2 * latticeRadius R k) ^ (p + 1) := by
  let F := badCellTestFamily (p + 1) μ R hR k z J v hcore
  exact F.riesz_oscillation_packing C G hC hg hlower (by norm_num) hJ s D hRiesz
    (z : Ambient d) (2 * latticeRadius R k) v
    (mul_pos (by norm_num) (latticeRadius_pos R hR k)) hv N hN
    (fun i _ => i.val.center_dist_top) (fun i _ => i.val.binary_radius)
    (fun i => (badCellWitness (p + 1) μ R hR k z J v i).direction)
    (fun i _ => (badCellWitness (p + 1) μ R hR k z J v i).direction_bound)
    (fun i _ => (badCellWitness (p + 1) μ R hR k z J v i).large_pairing.le)

theorem bad_support_descendants_mass_packing {p d : ℕ} [Nontrivial (Ambient d)]
    (μ : Measure (Ambient d)) [SFinite μ] (C G J v : ℝ)
    (hC : 0 < C) (hG : 0 < G) (hJ : 0 < J) (hv : 0 < v)
    (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r))
    (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated (p + 1) μ ε f) 2 μ ∧
        eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (N : ℕ) (hN : (1 / 2 : ℝ) ^ N ≤ smallRieszRadiusFraction (p + 1) G J v)
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (s : Finset (BadSupportDescendant (p + 1) μ R hR k z J v)) :
    ∑ i ∈ s, μ.real i.val.cell ≤
      latticeMassPackingConstant (p + 1) C G
        (rieszOscillationPackingConstant (p + 1) C G (1 / 8) J v D N) *
          μ.real (cleanSupportCell μ R hR k z) := by
  exact cell_mass_packing_of_radius_packing
    (ι := BadSupportDescendant (p + 1) μ R hR k z J v) (n := p + 1) (d := d)
    μ C G (rieszOscillationPackingConstant (p + 1) C G (1 / 8) J v D N) hC hG
    (rieszOscillationPackingConstant_pos (p + 1) C G (1 / 8) J v D N hC hG.le
      (by norm_num) hJ).le hg hlower R hR k hcore z
    (fun i : BadSupportDescendant (p + 1) μ R hR k z J v => i.val) s
    (bad_support_descendants_radius_packing μ C G J v hC hJ hv hg hlower D hRiesz
      N hN R hR k z hcore s)

theorem exists_uniform_bad_cell_carleson_constant (p d : ℕ) [Nontrivial (Ambient d)]
    (C G J v : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 < G) (hJ : 0 < J) (hv : 0 < v) :
    ∃ K : ℝ, 0 < K ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r)) →
      (∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated (p + 1) μ ε f) 2 μ ∧
          eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∀ s : Finset (BadSupportDescendant (p + 1) μ R hR k z J v),
        ∑ i ∈ s, μ.real i.val.cell ≤ K * μ.real (cleanSupportCell μ R hR k z) := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (smallRieszRadiusFraction_pos (p + 1) G J v hG.le hJ hv)
    (by norm_num : (1 / 2 : ℝ) < 1)
  let B := rieszOscillationPackingConstant (p + 1) C G (1 / 8) J v D N
  have hB : 0 < B := rieszOscillationPackingConstant_pos (p + 1) C G (1 / 8) J v D N
    hC hG.le (by norm_num) hJ
  refine ⟨latticeMassPackingConstant (p + 1) C G B,
    latticeMassPackingConstant_pos (p + 1) C G B hC hG hB, ?_⟩
  intro μ hg hlower hRiesz R hR k z hcore s
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  exact bad_support_descendants_mass_packing μ C G J v hC hG hJ hv hg hlower D hRiesz
    N hN.le R hR k z hcore s

end

end RieszRectifiability

end OAI
