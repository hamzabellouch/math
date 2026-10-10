import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.LatticeMassPacking
import OAI.Analysis.RieszRectifiability.Packing.CellHaarPairGeometry

namespace OAI

/-!
# Haar tests on AD-regular lattice cells

Admissible core radii remain admissible at later lattice levels. Global upper
growth makes the clean cells finite, while the lower AD estimate gives positive
inner-cell mass. These facts yield mean-zero, L²-normalized Haar tests and the
exact pairing formula in terms of the inner and outer cell means.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem lattice_core_admissible_at_later_level {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k l : ℕ) (hkl : k ≤ l)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8)) :
    AdmissibleRadius μ (latticeRadius R l / 8) := by
  refine ⟨div_pos (latticeRadius_pos R hR l) (by norm_num), ?_⟩
  exact (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
    (latticeRadius_antitone R hR.le hkl) (by norm_num))).trans hcore.2

theorem cleanSupportCell_finite_of_growth {n d : ℕ} (μ : Measure (Ambient d))
    (G : ℝ) (hg : GlobalUpperGrowth n G μ) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    μ (cleanSupportCell μ R hR k z) < ∞ := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  exact (measure_mono sdiff_subset).trans_lt (supportLatticeCell_compact μ R hR k z).measure_lt_top

theorem CellHaarPair.cells_finite {n d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k I : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (P : CellHaarPair μ R hR k z I) (G : ℝ) (hg : GlobalUpperGrowth n G μ) :
    μ P.innerCell < ∞ ∧ μ P.outerCell < ∞ :=
  ⟨cleanSupportCell_finite_of_growth μ G hg R hR (k + P.outerOffset + P.innerOffset) P.innerCenter,
    cleanSupportCell_finite_of_growth μ G hg R hR (k + P.outerOffset) P.outerCenter⟩

theorem CellHaarPair.inner_real_pos {n d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k I : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (P : CellHaarPair μ R hR k z I) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8)) : 0 < μ.real P.innerCell := by
  have ha := lattice_core_admissible_at_later_level μ R hR k
    (k + P.outerOffset + P.innerOffset) (by omega) hcore
  have hp := cleanSupportCell_measure_pos_finite μ C G hC hG hg hlower R hR
    (k + P.outerOffset + P.innerOffset) ha P.innerCenter
  exact ENNReal.toReal_pos hp.1.ne' hp.2.ne

theorem CellHaarPair.test_properties {n d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k I : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (P : CellHaarPair μ R hR k z I) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8)) :
    MemLp P.test 2 μ ∧ (∫ x, P.test x ∂μ) = 0 ∧ (∫ x, P.test x ^ 2 ∂μ) ≤ 1 ∧
      ∀ u : Ambient d → ℝ, MemLp u 2 μ →
        (∫ x, P.test x * u x ∂μ) = Real.sqrt (μ.real P.innerCell) *
          (cellMean (μ.restrict P.innerCell) u - cellMean (μ.restrict P.outerCell) u) := by
  have hf := P.cells_finite G hg
  have hp := P.inner_real_pos C G hC hG hg hlower hcore
  exact ⟨cellHaar_memLp μ P.innerCell P.outerCell P.inner_measurable P.outer_measurable hf.1 hf.2,
    cellHaar_mean_zero μ P.innerCell P.outerCell P.inner_measurable P.outer_measurable
      hf.1 hf.2 P.inner_subset_outer hp,
    cellHaar_sq_integral_le_one μ P.innerCell P.outerCell P.inner_measurable P.outer_measurable
      hf.1 hf.2 P.inner_subset_outer hp,
    fun u hu => cellHaar_pairing μ P.innerCell P.outerCell P.inner_measurable P.outer_measurable
      hf.1 hf.2 u hu⟩

end

end RieszRectifiability

end OAI
