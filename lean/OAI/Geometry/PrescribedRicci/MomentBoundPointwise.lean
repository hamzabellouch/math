import Mathlib

namespace OAI

/-! Moment Bound Pointwise. -/

noncomputable section
open Set Filter Topology MeasureTheory
namespace Anticanonical.SourceSmooth

lemma continuous_le_of_moments {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {w : X → ℝ} (hw : Continuous w) (hwn : ∀ x, 0 ≤ w x)
    (p : ℕ → ℝ) (hp : ∀ n, 0 < p n) (hpt : Tendsto p atTop atTop)
    {B : ℝ} (hB : 0 ≤ B)
    (hi : ∀ n, Integrable (fun x => w x ^ p n) μ)
    (hb : ∀ n, ∫ x, w x ^ p n ∂μ ≤ B ^ p n) : ∀ x, w x ≤ B := by
  intro x
  by_contra! hx
  obtain ⟨r,hrB,hrx⟩ := exists_between hx
  have hr : 0 < r := lt_of_le_of_lt hB hrB
  let U := {y | r < w y}
  have hU : IsOpen U := isOpen_lt continuous_const hw
  have hUm : 0 < μ.real U := ENNReal.toReal_pos (ne_of_gt (hU.measure_pos μ ⟨x,hrx⟩)) (by finiteness)
  have hbound (n : ℕ) : μ.real U ≤ (B/r)^(p n) := by
    have hs : U ⊆ {y | r^(p n) ≤ w y^(p n)} := fun y hy =>
      Real.rpow_le_rpow hr.le hy.le (hp n).le
    have hm := mul_meas_ge_le_integral_of_nonneg
      (ae_of_all μ (fun y => Real.rpow_nonneg (hwn y) (p n))) (hi n) (r^(p n))
    have hh : r^(p n)*μ.real U ≤ B^(p n) :=
      (mul_le_mul_of_nonneg_left (measureReal_mono hs) (Real.rpow_nonneg hr.le _)).trans (hm.trans (hb n))
    rw [Real.div_rpow hB hr.le]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hr _)).mpr
    simpa only [mul_comm] using hh
  have hlim : Tendsto (fun n => (B/r)^(p n)) atTop (𝓝 0) :=
    (tendsto_rpow_atTop_of_base_lt_one (B/r)
      (by have hh := div_nonneg hB hr.le; linarith)
      ((div_lt_one hr).mpr hrB)).comp hpt
  have hz : μ.real U ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hbound)
  exact (not_le_of_gt hUm) hz

end Anticanonical.SourceSmooth

end

end OAI
