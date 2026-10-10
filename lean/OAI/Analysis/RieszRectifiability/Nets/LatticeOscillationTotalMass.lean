import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.LatticeOscillationCarleson

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem measure_tsum_le_of_real_finset_bounds {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A : ι → Set X) (B : ℝ)
    (hfinite : ∀ i, μ (A i) ≠ ∞)
    (hbound : ∀ s : Finset ι, ∑ i ∈ s, μ.real (A i) ≤ B) :
    ∑' i, μ (A i) ≤ ENNReal.ofReal B := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  have heq : ∑ i ∈ s, μ (A i) = ENNReal.ofReal (∑ i ∈ s, μ.real (A i)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => measureReal_nonneg)]
    apply Finset.sum_congr rfl
    intro i _
    exact (ENNReal.ofReal_toReal (hfinite i)).symm
  rw [heq]
  exact ENNReal.ofReal_le_ofReal (hbound s)

theorem exists_uniform_bad_descendant_total_mass (p d : ℕ) [Nontrivial (Ambient d)]
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
        ∑' i : BadSupportDescendant (p + 1) μ R hR k z J v, μ i.val.cell ≤
          ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨K, hK, hpack⟩ := exists_uniform_bad_cell_carleson_constant p d C G J v D hC hG hJ hv
  refine ⟨K, hK, ?_⟩
  intro μ hg hlower hRiesz R hR k z hcore
  have hb := measure_tsum_le_of_real_finset_bounds μ
    (fun i : BadSupportDescendant (p + 1) μ R hR k z J v => i.val.cell)
    (K * μ.real (cleanSupportCell μ R hR k z))
    (fun i => ((i.val.measure_upper G hg).trans_lt ENNReal.ofReal_lt_top).ne)
    (hpack μ hg hlower hRiesz R hR k z hcore)
  have hf := (cleanSupportCell_measure_pos_finite μ C G hC hG hg hlower R hR k hcore z).2.ne
  simpa only [ENNReal.ofReal_mul hK.le, Measure.real, ENNReal.ofReal_toReal hf] using! hb

end

end RieszRectifiability

end OAI
