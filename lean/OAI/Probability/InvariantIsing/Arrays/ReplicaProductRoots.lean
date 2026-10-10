import OAI.Probability.InvariantIsing.Arrays.ReplicaProductPrimitives

namespace OAI

/-! The root of the replica-product path. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

lemma pathSymbol_root_tendsto (d : ℝ) (a : ℝ → ℝ) (ha : Measurable a)
    {A : ℝ} (haB : ∀ u, |a u| ≤ A) {r : ℝ}
    (hr : Tendsto a (𝓝[>] 0) (𝓝 r)) :
    Tendsto (pathSymbol d a) (𝓝[>] 0) (𝓝 (d - ∫ u in 0..1, a u)) := by
  have hi (s t : ℝ) : IntervalIntegrable a volume s t :=
    intervalIntegrable_of_measurable_abs_le ha haB s t
  have ht := ((continuous_tail_integral hi 1).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hz : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  change Tendsto (fun s => d - s * a s - ∫ u in s..1, a u) _ _
  simpa only [zero_mul, sub_zero] using
    ((tendsto_const_nhds.sub (hz.mul hr)).sub ht :
      Tendsto (fun s => d - s * a s - ∫ u in s..1, a u) (𝓝[>] 0)
        (𝓝 (d - 0 * r - ∫ u in 0..1, a u)))

theorem replicaProductPath_root_tendsto (da db : ℝ) (a b : ℝ → ℝ)
    (ha : Measurable a) (hb : Measurable b) {A B : ℝ} (hA : 0 ≤ A)
    (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) {ra rb : ℝ}
    (hra : Tendsto a (𝓝[>] 0) (𝓝 ra)) (hrb : Tendsto b (𝓝[>] 0) (𝓝 rb)) :
    Tendsto (replicaProductPath da a db b) (𝓝[>] 0)
      (𝓝 ((da - ∫ u in 0..1, a u) * rb + ra * (db - ∫ u in 0..1, b u))) := by
  have hab (u : ℝ) : |a u * b u| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul (haB u) (hbB u) (abs_nonneg _) hA
  have hi (s t : ℝ) : IntervalIntegrable (fun u => a u * b u) volume s t :=
    intervalIntegrable_of_measurable_abs_le (ha.mul hb) hab s t
  have hp := ((intervalIntegral.continuous_primitive hi 0).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hz : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have he := (((pathSymbol_root_tendsto da a ha haB hra).mul hrb).add
    (hra.mul (pathSymbol_root_tendsto db b hb hbB hrb))).add (hz.mul (hra.mul hrb)) |>.sub hp
  change Tendsto (fun s => pathSymbol da a s * b s + a s * pathSymbol db b s +
    s * (a s * b s) - ∫ u in 0..s, a u * b u) _ _
  simpa only [intervalIntegral.integral_same, zero_mul, add_zero, sub_zero] using he

end InvariantIsing

end

end OAI
