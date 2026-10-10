import OAI.Analysis.CircleDomains.Rigidity.TraceCompression
import OAI.Analysis.CircleDomains.LengthArea
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

/-! Tonelli's theorem selects lines with finite total interval cost.
The union of the remaining active intervals consequently has vanishing
outer length. Overlaps between the intervals require no disjointness. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] Classical.propDecidable

 theorem ae_finite_line_incidence {A : ℕ → Set ℝ}
    (hA : ∀ j, MeasurableSet (A j)) (a : ℕ → ℝ≥0∞)
    (hsum : (∑' j, a j * volume (A j)) ≠ ∞) :
    ∀ᵐ t ∂volume, (∑' j, (A j).indicator (fun _ => a j) t) < ∞ := by
  have hm (j : ℕ) : Measurable ((A j).indicator (fun _ : ℝ => a j)) :=
    measurable_const.indicator (hA j)
  apply ae_lt_top (Measurable.tsum hm)
  rw [lintegral_tsum (fun j => (hm j).aemeasurable)]
  simpa only [lintegral_indicator (hA _),lintegral_const,Measure.restrict_apply_univ] using hsum

 def lineTailIntervals (I A : ℕ → Set ℝ) (t : ℝ) (N : ℕ) : Set ℝ :=
  ⋃ k : ℕ, if t ∈ A (k+N) then I (k+N) else ∅

 theorem lineTailIntervals_measurable {I A : ℕ → Set ℝ}
    (hI : ∀ j, MeasurableSet (I j)) (t : ℝ) (N : ℕ) :
    MeasurableSet (lineTailIntervals I A t N) := by
  apply MeasurableSet.iUnion
  intro k
  split_ifs
  · exact hI _
  · exact MeasurableSet.empty

 theorem lineTailIntervals_volume_tendsto {I A : ℕ → Set ℝ} {t : ℝ}
    (hfinite : (∑' j, (A j).indicator (fun _ => volume (I j)) t) ≠ ∞) :
    Tendsto (fun N => volume (lineTailIntervals I A t N)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ENNReal.tendsto_sum_nat_add _ hfinite) (fun _ => bot_le)
  intro N
  apply (measure_iUnion_le _).trans
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases ht : t ∈ A (k+N)
  · simp [ht]
  · simp [ht]

 theorem ae_lineTailIntervals_volume_tendsto {I A : ℕ → Set ℝ}
    (hA : ∀ j, MeasurableSet (A j))
    (hsum : (∑' j, volume (I j)*volume (A j)) ≠ ∞) :
    ∀ᵐ t ∂volume, Tendsto (fun N => volume (lineTailIntervals I A t N)) atTop (𝓝 0) := by
  filter_upwards [ae_finite_line_incidence hA (fun j => volume (I j)) hsum] with t ht
  exact lineTailIntervals_volume_tendsto ht.ne

/-- Square-summable interval lengths and balloon radii pay for almost
all transverse lines. The center positions are unrestricted. -/
 theorem ae_balloon_line_tails {I : ℕ → Set ℝ} {d : ℕ → ℝ}
    (hd : ∀ j, 0 ≤ d j) (c : ℕ → ℝ)
    (hI : ∀ j, volume (I j) ≠ ∞)
    (hIsq : Summable (fun j => volume.real (I j)^2))
    (hdsq : Summable (fun j => d j^2)) :
    ∀ᵐ t ∂volume, Tendsto (fun N => volume
      (lineTailIntervals I (fun j => Ioo (c j-d j) (c j+d j)) t N)) atTop (𝓝 0) := by
  apply ae_lineTailIntervals_volume_tendsto (fun _ => measurableSet_Ioo)
  have hs := (LengthArea.summable_mul_of_squares hIsq hdsq).mul_right 2
  have he (j : ℕ) : volume (I j)*volume (Ioo (c j-d j) (c j+d j)) =
      ENNReal.ofReal (volume.real (I j)*d j*2) := by
    simp only [measureReal_def]
    rw [Real.volume_Ioo,show c j+d j-(c j-d j) = d j*2 by ring,
      ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (hd j)),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (hI j),
      ENNReal.ofReal_mul (hd j),mul_assoc]
  simpa only [he] using hs.tsum_ofReal_ne_top

end CircleDomainRigidity

end

end OAI
