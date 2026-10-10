import OAI.Analysis.LipschitzHilbert.Fourier.ShortPositiveConvolution
import OAI.Analysis.LipschitzHilbert.Fourier.LongPositiveConvolution
import OAI.Analysis.LipschitzHilbert.Estimates.RawBMOMoments
import OAI.Analysis.LipschitzHilbert.Fourier.VariationLineBMO

namespace OAI

/-! The actual positive convolution majorant for the error terms. Source
size and source-sum bounds remain explicit; BMO is derived for this
majorant rather than assumed for every function it dominates. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

structure LineErrorSources (N : ℕ) where
  topLength : ℝ
  topLength_pos : 0 < topLength
  sourceBound : ℝ
  sourceBound_nonneg : 0 ≤ sourceBound
  sumBound : ℝ
  sumBound_nonneg : 0 ≤ sumBound
  source : Fin N → ℝ → ℝ
  measurable_source : ∀ j, Measurable (source j)
  source_nonneg : ∀ j s, 0 ≤ source j s
  source_bound : ∀ j s, source j s ≤ sourceBound
  source_sum : ∀ s, ∑ j, source j s ≤ sumBound

namespace LineErrorSources

attribute [local instance] Classical.propDecidable

variable {N : ℕ}

def length (P : LineErrorSources N) (j : Fin N) : ℝ := P.topLength / (2 : ℝ)^j.val
def term (P : LineErrorSources N) (j : Fin N) : ℝ → ℝ := positiveConvolution (P.length j) (P.source j)
def majorant (P : LineErrorSources N) (x : ℝ) : ℝ := ∑ j, P.term j x
def shortPart (P : LineErrorSources N) (r x : ℝ) : ℝ := ∑ j, if P.length j ≤ r then P.term j x else 0
def longPart (P : LineErrorSources N) (r x : ℝ) : ℝ := ∑ j, if r < P.length j then P.term j x else 0
def meanConstant (P : LineErrorSources N) : ℝ := (1024 * Real.pi^2) * P.sumBound
def oscillationConstant (P : LineErrorSources N) : ℝ := 240 * Real.pi * P.sourceBound

theorem length_pos (P : LineErrorSources N) (j : Fin N) : 0 < P.length j := by
  exact div_pos P.topLength_pos (pow_pos (by norm_num) _)

theorem source_norm_bound (P : LineErrorSources N) (j : Fin N) (s : ℝ) :
    ‖P.source j s‖ ≤ P.sourceBound := by
  rw [Real.norm_eq_abs, abs_of_nonneg (P.source_nonneg j s)]
  exact P.source_bound j s

theorem term_nonneg (P : LineErrorSources N) (j : Fin N) (x : ℝ) : 0 ≤ P.term j x :=
  positiveConvolution_nonneg (P.length_pos j) (P.source_nonneg j) x

theorem term_continuous (P : LineErrorSources N) (j : Fin N) : Continuous (P.term j) :=
  positiveConvolution_continuous (P.measurable_source j) P.sourceBound_nonneg (P.length_pos j) (P.source_norm_bound j)

theorem majorant_nonneg (P : LineErrorSources N) (x : ℝ) : 0 ≤ P.majorant x :=
  Finset.sum_nonneg (fun j _ => P.term_nonneg j x)

theorem majorant_continuous (P : LineErrorSources N) : Continuous P.majorant :=
  continuous_finsetSum _ (fun j _ => P.term_continuous j)

theorem shortPart_nonneg (P : LineErrorSources N) (r x : ℝ) : 0 ≤ P.shortPart r x :=
  Finset.sum_nonneg (fun j _ => by split_ifs; exact P.term_nonneg j x; exact le_rfl)

theorem shortPart_continuous (P : LineErrorSources N) (r : ℝ) : Continuous (P.shortPart r) := by
  apply continuous_finsetSum
  intro j _
  by_cases hj : P.length j ≤ r
  · simpa only [ite_eq_left hj] using P.term_continuous j
  · simp only [ite_eq_right hj]
    exact continuous_const

theorem longPart_continuous (P : LineErrorSources N) (r : ℝ) : Continuous (P.longPart r) := by
  apply continuous_finsetSum
  intro j _
  by_cases hj : r < P.length j
  · simpa only [ite_eq_left hj] using P.term_continuous j
  · simp only [ite_eq_right hj]
    exact continuous_const

theorem majorant_split (P : LineErrorSources N) (r x : ℝ) :
    P.majorant x = P.shortPart r x + P.longPart r x := by
  unfold majorant shortPart longPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : P.length j ≤ r
  · simp only [ite_eq_left hj, ite_eq_right (not_lt.mpr hj), add_zero]
  · simp only [ite_eq_right hj, ite_eq_left (lt_of_not_ge hj), zero_add]

theorem shortPart_integral (P : LineErrorSources N) (u r : ℝ) (hr : 0 < r) :
    (∫ x in Icc (u-r) (u+r), P.shortPart r x) ≤ P.meanConstant * r :=
  short_positiveConvolution_integral P.source P.length P.length_pos P.measurable_source
    P.source_nonneg P.sumBound_nonneg P.source_sum u r hr

theorem longPart_oscillation (P : LineErrorSources N) (u r : ℝ) (hr : 0 < r)
    {x y : ℝ} (hx : x ∈ Icc (u-r) (u+r)) (hy : y ∈ Icc (u-r) (u+r)) :
    |P.longPart r x - P.longPart r y| ≤ P.oscillationConstant :=
  long_positiveConvolution_oscillation P.source P.measurable_source P.sourceBound_nonneg
    P.topLength_pos P.source_norm_bound u r hr hx hy

theorem majorant_mean_oscillation (P : LineErrorSources N) (g : FiniteLineGrid) :
    g.HasFullMeanOscillationBound P.majorant (2 * P.meanConstant + P.oscillationConstant) := by
  intro level i _
  let r := g.meshWidth level / 2
  let u := g.origin + g.meshWidth level * i + r
  have hr : 0 < r := half_pos (g.meshWidth_pos level)
  have hcell : g.cell level i = Ico (u-r) (u+r) := by
    dsimp [FiniteLineGrid.cell,u,r]
    congr 1 <;> ring
  have hs := g.continuous_integrable_cell (P.shortPart_continuous r) level i
  have hl := g.continuous_integrable_cell (P.longPart_continuous r) level i
  have hshort : (∫ x in g.cell level i, ‖P.shortPart r x‖) ≤
      P.meanConstant * (volume.restrict (g.cell level i)).real univ := by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (P.shortPart_nonneg r _)]
    rw [g.cell_mass, hcell, ← integral_Icc_eq_integral_Ico]
    apply (P.shortPart_integral u r hr).trans
    have hK : 0 ≤ P.meanConstant := by
      have := P.sumBound_nonneg
      unfold meanConstant
      positivity
    exact mul_le_mul_of_nonneg_left (by dsimp [r]; linarith [g.meshWidth_pos level]) hK
  have hlong : ∀ᵐ x ∂volume.restrict (g.cell level i), ∀ᵐ y ∂volume.restrict (g.cell level i),
      ‖P.longPart r x - P.longPart r y‖ ≤ P.oscillationConstant := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    rw [hcell] at hx hy
    simpa only [Real.norm_eq_abs] using P.longPart_oscillation u r hr
      (Ico_subset_Icc_self hx) (Ico_subset_Icc_self hy)
  have h := short_long_mean_oscillation (volume.restrict (g.cell level i))
    (P.shortPart r) (P.longPart r) hs hl (by rw [g.cell_mass]; exact g.meshWidth_pos level) hshort hlong
  simp_rw [← P.majorant_split r] at h
  simpa only [Real.norm_eq_abs, g.cellMean_eq_integralAverage, g.cell_mass] using h

end LineErrorSources
end LipschitzHilbert

end

end OAI
