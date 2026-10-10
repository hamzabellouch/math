import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.HaarRieszBessel
import OAI.Analysis.RieszRectifiability.Packing.HaarCellMassRatio

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem bounded_depth_riesz_average_gap_packing {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k I : ℕ) (hI : 0 < I) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (P : (i : SupportCellDescendant μ R hR k z) →
      CellHaarPair μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ I)
    (s : Finset (SupportCellDescendant μ R hR k z)) (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated n μ ε f) 2 μ ∧
        eLpNorm (truncated n μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (ε : ℝ) (hε : 0 < ε) (f : Ambient d → ℝ) (hf : MemLp f 2 μ)
    (e : SupportCellDescendant μ R hR k z → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1)
    (v : ℝ) (hv : 0 < v)
    (hgap : ∀ i ∈ s, v ≤
      |cellMean (μ.restrict (P i).innerCell) (fun x => inner ℝ (e i) (truncated n μ ε f x)) -
        cellMean (μ.restrict (P i).outerCell) (fun x => inner ℝ (e i) (truncated n μ ε f x))|) :
    ∑ i ∈ s, μ.real i.cell ≤
      ((haarCellMassRatio n C G I * (I : ℝ) * (D : ℝ) ^ 2) * ∫ x, f x ^ 2 ∂μ) / v ^ 2 := by
  let a := fun i : SupportCellDescendant μ R hR k z =>
    cellMean (μ.restrict (P i).innerCell) (fun x => inner ℝ (e i) (truncated n μ ε f x)) -
      cellMean (μ.restrict (P i).outerCell) (fun x => inner ℝ (e i) (truncated n μ ε f x))
  have hK : 0 ≤ haarCellMassRatio n C G I := (haarCellMassRatio_pos n C G I hC hG).le
  have hm (i : SupportCellDescendant μ R hR k z) :
      μ.real i.cell ≤ haarCellMassRatio n C G I * μ.real (P i).innerCell :=
    (P i).parent_mass_le_inner C G hC hG hg hlower
      (lattice_core_admissible_at_later_level μ R hR k (k + i.depth)
        (Nat.le_add_right k i.depth) hcore)
  have hterm (i : SupportCellDescendant μ R hR k z) (hi : i ∈ s) :
      μ.real i.cell * v ^ 2 ≤ haarCellMassRatio n C G I * (μ.real (P i).innerCell * a i ^ 2) := by
    have hs : v ^ 2 ≤ a i ^ 2 := by
      simpa only [← pow_two, sq_abs] using! mul_self_le_mul_self hv.le (hgap i hi)
    calc
      _ ≤ (haarCellMassRatio n C G I * μ.real (P i).innerCell) * v ^ 2 :=
        mul_le_mul_of_nonneg_right (hm i) (sq_nonneg v)
      _ = haarCellMassRatio n C G I * (μ.real (P i).innerCell * v ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hs measureReal_nonneg) hK
  have hb := bounded_depth_riesz_average_bessel μ C G hC hG hg hlower R hR k I hI z hcore
    P s D hRiesz ε hε f hf e he
  apply (le_div_iff₀ (sq_pos_of_pos hv)).mpr
  calc
    _ = ∑ i ∈ s, μ.real i.cell * v ^ 2 := Finset.sum_mul ..
    _ ≤ ∑ i ∈ s, haarCellMassRatio n C G I * (μ.real (P i).innerCell * a i ^ 2) :=
      Finset.sum_le_sum hterm
    _ = haarCellMassRatio n C G I * ∑ i ∈ s, μ.real (P i).innerCell * a i ^ 2 :=
      (Finset.mul_sum ..).symm
    _ ≤ haarCellMassRatio n C G I * (((I : ℝ) * (D : ℝ) ^ 2) * ∫ x, f x ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left hb hK
    _ = _ := by ring

end

end RieszRectifiability

end OAI
