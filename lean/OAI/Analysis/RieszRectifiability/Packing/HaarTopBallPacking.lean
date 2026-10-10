import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.HaarAverageGapPacking
import OAI.Analysis.RieszRectifiability.Limits.FixedCutoffPairingLimit

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def topCellBallIndicator {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) (A : ℝ) : Ambient d → ℝ :=
  (ball (z : Ambient d) (A * latticeRadius R k)).indicator (fun _ => 1)

theorem top_cell_ball_real_mass_bound {n d : ℕ}
    (μ : Measure (Ambient d)) (C G A : ℝ) (hC : 0 < C) (hG : 0 < G) (hA : 0 < A)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8)) :
    μ.real (ball (z : Ambient d) (A * latticeRadius R k)) ≤
      (C * G * (8 * A) ^ n) * μ.real (cleanSupportCell μ R hR k z) := by
  have hr := latticeRadius_pos R hR k
  have hu : μ.real (ball (z : Ambient d) (A * latticeRadius R k)) ≤
      G * (A * latticeRadius R k) ^ n :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hg.2 z _ (mul_pos hA hr))
  have hl := (cleanSupportCell_real_measure_bounds μ C G hC hG hg hlower R hR k hcore z).1
  have hid : G * (A * latticeRadius R k) ^ n =
      (C * G * (8 * A) ^ n) * ((latticeRadius R k / 8) ^ n / C) := by
    simp only [mul_pow, div_pow]
    field_simp
  exact hu.trans (hid.le.trans (mul_le_mul_of_nonneg_left hl (by positivity)))

def haarTopBallPackingConstant (n : ℕ) (C G A v : ℝ) (D : ℝ≥0) (I : ℕ) : ℝ :=
  (haarCellMassRatio n C G I * (I : ℝ) * (D : ℝ) ^ 2) * (C * G * (8 * A) ^ n) / v ^ 2

theorem bounded_depth_haar_top_ball_packing {n d : ℕ}
    (μ : Measure (Ambient d)) (C G A : ℝ) (hC : 0 < C) (hG : 0 < G) (hA : 0 < A)
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
    (ε : ℝ) (hε : 0 < ε)
    (e : SupportCellDescendant μ R hR k z → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1)
    (v : ℝ) (hv : 0 < v)
    (hgap : ∀ i ∈ s, v ≤
      |cellMean (μ.restrict (P i).innerCell)
          (fun x => inner ℝ (e i) (truncated n μ ε (topCellBallIndicator μ R hR k z A) x)) -
        cellMean (μ.restrict (P i).outerCell)
          (fun x => inner ℝ (e i) (truncated n μ ε (topCellBallIndicator μ R hR k z A) x))|) :
    ∑ i ∈ s, μ.real i.cell ≤
      haarTopBallPackingConstant n C G A v D I * μ.real (cleanSupportCell μ R hR k z) := by
  have hf : MemLp (topCellBallIndicator μ R hR k z A) 2 μ ∧
      (∫ x, topCellBallIndicator μ R hR k z A x ^ 2 ∂μ) =
        μ.real (ball (z : Ambient d) (A * latticeRadius R k)) :=
    ball_indicator_one_memLp_and_sq_integral n G μ hg z (A * latticeRadius R k)
      (mul_pos hA (latticeRadius_pos R hR k))
  have hb := bounded_depth_riesz_average_gap_packing μ C G hC hG hg hlower R hR k I hI z hcore
    P s D hRiesz ε hε (topCellBallIndicator μ R hR k z A) hf.1 e he v hv hgap
  rw [hf.2] at hb
  have hm := top_cell_ball_real_mass_bound μ C G A hC hG hA hg hlower R hR k z hcore
  have hK : 0 ≤ haarCellMassRatio n C G I * (I : ℝ) * (D : ℝ) ^ 2 := by
    have hp := haarCellMassRatio_pos n C G I hC hG
    positivity
  calc
    _ ≤ _ := hb
    _ ≤ (haarCellMassRatio n C G I * (I : ℝ) * (D : ℝ) ^ 2) *
        ((C * G * (8 * A) ^ n) * μ.real (cleanSupportCell μ R hR k z)) / v ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm hK) (sq_nonneg v)
    _ = _ := by unfold haarTopBallPackingConstant; ring

end

end RieszRectifiability

end OAI
