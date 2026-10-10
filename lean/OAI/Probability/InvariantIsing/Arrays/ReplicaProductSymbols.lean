import OAI.Probability.InvariantIsing.Arrays.ReplicaProductPrimitives

namespace OAI

/-! Multiplicativity of replica-product symbols for measurable bounded
paths, including paths with jumps. -/

noncomputable section

open MeasureTheory Set

namespace InvariantIsing

theorem replicaProductPath_symbol (a b : ℝ → ℝ) (ha : Measurable a) (hb : Measurable b)
    {A B : ℝ} (hA : 0 ≤ A) (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B)
    (da db : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    pathSymbol (replicaProductDiagonal da db a b) (replicaProductPath da a db b) s =
      pathSymbol da a s * pathSymbol db b s := by
  have hai (v w : ℝ) : IntervalIntegrable a volume v w :=
    intervalIntegrable_of_measurable_abs_le ha haB v w
  have hbi (v w : ℝ) : IntervalIntegrable b volume v w :=
    intervalIntegrable_of_measurable_abs_le hb hbB v w
  have hab (u : ℝ) : |a u * b u| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul (haB u) (hbB u) (abs_nonneg _) hA
  have habi (v w : ℝ) : IntervalIntegrable (fun u => a u * b u) volume v w :=
    intervalIntegrable_of_measurable_abs_le (ha.mul hb) hab v w
  let Ta : ℝ → ℝ := fun u => ∫ v in u..1, a v
  let Tb : ℝ → ℝ := fun u => ∫ v in u..1, b v
  let P : ℝ → ℝ := fun u => ∫ v in 0..u, a v * b v
  have hTa : ContinuousOn Ta (uIcc s 1) := (absolutelyContinuous_tail_integral (hai s 1)).continuousOn
  have hTb : ContinuousOn Tb (uIcc s 1) := (absolutelyContinuous_tail_integral (hbi s 1)).continuousOn
  have hP₀ : AbsolutelyContinuousOnInterval P 0 1 :=
    (habi 0 1).absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hsub : uIcc s 1 ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le hs.2, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hs.1 le_rfl
  have hP : IntervalIntegrable P volume s 1 :=
    (hP₀.mono hsub).continuousOn.intervalIntegrable
  have hM : IntervalIntegrable (fun u => u * (a u * b u) + P u) volume s 1 :=
    ((habi s 1).continuousOn_mul continuousOn_id).add hP
  have hT : IntervalIntegrable (fun u => a u * Tb u + b u * Ta u) volume s 1 :=
    ((hai s 1).mul_continuousOn hTb).add ((hbi s 1).mul_continuousOn hTa)
  have hL : IntervalIntegrable (fun u => da * b u + a u * db) volume s 1 :=
    ((hbi s 1).const_mul da).add ((hai s 1).mul_const db)
  have hc (u : ℝ) : replicaProductPath da a db b u =
      da * b u + a u * db -
        ((u * (a u * b u) + P u) + (a u * Tb u + b u * Ta u)) := by
    unfold replicaProductPath pathSymbol
    dsimp only [Ta, Tb, P]
    ring
  have ht : (∫ u in s..1, replicaProductPath da a db b u) =
      da * Tb s + Ta s * db -
        (((∫ u in 0..1, a u * b u) - s * P s) + Ta s * Tb s) := by
    simp_rw [hc]
    rw [intervalIntegral.integral_sub hL (hM.add hT),
      intervalIntegral.integral_add ((hbi s 1).const_mul da) ((hai s 1).mul_const db),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_add hM hT]
    have hm := integral_head_moment hs (habi 0 1)
    have htp := integral_tail_product (hai s 1) (hbi s 1)
    change (∫ u in s..1, u * (a u * b u) + P u) = _ at hm
    change (∫ u in s..1, a u * Tb u + b u * Ta u) = Ta s * Tb s at htp
    rw [hm, htp]
  have hfull : (∫ u, a u * b u ∂pathMeasure) = ∫ u in 0..1, a u * b u := by
    unfold pathMeasure
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  unfold pathSymbol replicaProductDiagonal
  rw [ht, hfull, hc]
  dsimp only [Ta, Tb, P]
  ring

end InvariantIsing

end

end OAI
