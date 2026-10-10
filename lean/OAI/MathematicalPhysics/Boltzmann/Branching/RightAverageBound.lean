import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

section

/-! # Approaching a time from a prescribed full-measure set on its right -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness

theorem exists_right_good_sequence {P : ℝ → Prop} (hP : ∀ᵐ t ∂volume, P t) (t : ℝ) :
    ∃ s : ℕ → ℝ, (∀ n, t < s n ∧ s n < t+1/((n:ℝ)+1) ∧ P (s n)) ∧
      Tendsto s atTop (𝓝 t) := by
  have hx (n : ℕ) : ∃ s, t < s ∧ s < t+1/((n:ℝ)+1) ∧ P s := by
    have hδ : 0 < 1/((n:ℝ)+1) := by positivity
    have hm : (volume : Measure ℝ) (Ioo t (t+1/((n:ℝ)+1))) ≠ 0 := by
      rw [Real.volume_Ioo]
      exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    obtain ⟨s,hs,hsp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hm (ae_restrict_of_ae hP)
    exact ⟨s,hs.1,hs.2,hsp⟩
  choose s hs using hx
  refine ⟨s,hs,?_⟩
  have hlim : Tendsto (fun n : ℕ => t+1/((n:ℝ)+1)) atTop (𝓝 t) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => (hs n).1.le) (fun n => (hs n).2.1.le)

end BoltzmannNonuniqueness

end

end

section

/-! # A joint bound on every right interval gives an almost-everywhere pointwise bound -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness

theorem ae_bound_of_right_integral_bound {H D : ℝ → ℝ} {B C : ℝ} (hB : 0 ≤ B)
    (hH : IntervalIntegrable H volume 0 B)
    (hbudget : ∀ t s : ℝ, 0 ≤ t → t < s → s ≤ B →
      (∫ r in t..s, H r)+(s-t)*D t ≤ (s-t)*C) :
    ∀ᵐ t ∂volume, t ∈ Ico 0 B → H t+D t ≤ C := by
  filter_upwards [hH.ae_hasDerivAt_integral] with t ht htB
  have htt : t ∈ uIcc 0 B := by simpa only [uIcc_of_le hB] using ⟨htB.1,htB.2.le⟩
  have hd := ht htt t htt
  have hl := hd.tendsto_slope_zero_right.add_const (D t)
  apply le_of_tendsto hl
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr htB.2)] with h hh
  have hb := hbudget t (t+h) htB.1 (by linarith [hh.1]) (by linarith [hh.2])
  simp only [intervalIntegral.integral_same,sub_zero,smul_eq_mul]
  change h⁻¹*(∫ r in t..(t+h), H r)+D t ≤ C
  calc
    _ = ((∫ r in t..(t+h), H r)+h*D t)/h := by field_simp [ne_of_gt hh.1]
    _ ≤ C := (div_le_iff₀ hh.1).mpr (by nlinarith only [hb])

end BoltzmannNonuniqueness

end

end

end OAI
