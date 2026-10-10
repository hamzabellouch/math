import OAI.Geometry.EinsteinFour.JacobiRiemann
import OAI.Geometry.EinsteinFour.SineAverage
import OAI.Geometry.EinsteinFour.ScalarDirichlet

namespace OAI

/-! Convergence of the normalized scalar-mode curvature average. -/

namespace PositiveEinsteinFour.Jacobi

open Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def interiorMean (f : ℝ → E) (N : ℕ) : E :=
  (1 / ((N : ℝ) + 1)) • ∑ i : Fin N, f ((i.val + 1) / ((N : ℝ) + 1))

theorem interiorMean_tendsto {f : ℝ → E} {L : ℝ}
    (hL : 0 ≤ L) (hc : Continuous f) (hf0 : f 0 = 0)
    (hf : ∀ s r, ‖f s - f r‖ ≤ L * |s - r|) :
    Tendsto (interiorMean f) atTop (nhds (∫ s in (0 : ℝ)..1, f s)) := by
  have hs (N : ℕ) : (∑ i : Fin N, f ((i.val + 1) / ((N : ℝ) + 1))) =
      ∑ i ∈ Finset.range (N + 1), f ((i : ℝ) / ((N : ℝ) + 1)) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div, hf0, add_zero]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Fin.sum_univ_eq_sum_range
        (fun i : ℕ => f (((i : ℝ) + 1) / ((N : ℝ) + 1))) N)
  have h := (uniform_mesh_tendsto_integral (by norm_num : (0 : ℝ) ≤ 1) hL hc hf).comp
    (show Tendsto (fun N : ℕ => N + 1) atTop atTop from tendsto_add_atTop_nat 1)
  convert h using 1
  funext N
  rw [interiorMean, hs]
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul]

theorem sineWeight_at_node (N : ℕ) (i : Fin N) :
    Averages.sineWeight ((i.val + 1) / ((N : ℝ) + 1)) = 2 * firstSineVector N i ^ 2 := by
  rw [Averages.sineWeight_eq]
  change 2 * Real.sin (Real.pi * ((i.val + 1) / ((N : ℝ) + 1))) ^ 2 =
    2 * Real.sin (((i.val : ℝ) + 1) * (Real.pi / ((N : ℝ) + 1))) ^ 2
  congr 1
  apply congrArg (fun z : ℝ => Real.sin z ^ 2)
  ring

def modeAverage (A : ℝ → E) (N : ℕ) : E :=
  ∑ i : Fin N, unitFirstSineVector N i ^ 2 • A ((i.val + 1) / ((N : ℝ) + 1))

omit [CompleteSpace E] in
theorem modeAverage_eq_ratio (A : ℝ → E) {N : ℕ} (hN : 0 < N) :
    modeAverage A N =
      (interiorMean Averages.sineWeight N)⁻¹ •
        interiorMean (fun s => Averages.sineWeight s • A s) N := by
  have hs : 0 < firstSineNormSq N := firstSineNormSq_pos hN
  have hM : (N : ℝ) + 1 ≠ 0 := by positivity
  have hd : interiorMean Averages.sineWeight N =
      (2 / ((N : ℝ) + 1)) * firstSineNormSq N := by
    simp only [interiorMean, sineWeight_at_node, smul_eq_mul, ← Finset.mul_sum]
    change (1 / ((N : ℝ) + 1)) * (2 * firstSineNormSq N) = _
    ring
  have hu : interiorMean (fun s => Averages.sineWeight s • A s) N =
      (2 / ((N : ℝ) + 1)) •
        (∑ i : Fin N, firstSineVector N i ^ 2 • A ((i.val + 1) / ((N : ℝ) + 1))) := by
    simp only [interiorMean, sineWeight_at_node, mul_smul]
    rw [← Finset.smul_sum, smul_smul]
    congr 1
    ring
  have hm : modeAverage A N = (1 / firstSineNormSq N) •
      (∑ i : Fin N, firstSineVector N i ^ 2 • A ((i.val + 1) / ((N : ℝ) + 1))) := by
    unfold modeAverage unitFirstSineVector
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, mul_smul,
      div_pow, one_pow, Real.sq_sqrt hs.le]
    rw [← Finset.smul_sum]
  rw [hm, hd, hu, smul_smul]
  congr 1
  field_simp [hM, hs.ne']

theorem sineWeight_lipschitz (s r : ℝ) :
    ‖Averages.sineWeight s - Averages.sineWeight r‖ ≤ 2 * Real.pi * |s - r| := by
  have hid : Averages.sineWeight s - Averages.sineWeight r =
      Real.cos (2 * Real.pi * r) - Real.cos (2 * Real.pi * s) := by
    unfold Averages.sineWeight
    ring
  rw [hid, Real.norm_eq_abs]
  calc
    _ ≤ |2 * Real.pi * r - 2 * Real.pi * s| := Real.abs_cos_sub_cos_le _ _
    _ = 2 * Real.pi * |s - r| := by
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi), abs_sub_comm]

/-- The normalized discrete sine mode converges to the actual sine-weighted
integral. Only regularity of the weighted curvature curve is used. -/
theorem modeAverage_tendsto {A : ℝ → E} {L : ℝ}
    (hL : 0 ≤ L) (hc : Continuous (fun s => Averages.sineWeight s • A s))
    (hLip : ∀ s r, ‖Averages.sineWeight s • A s - Averages.sineWeight r • A r‖ ≤
      L * |s - r|) :
    Tendsto (modeAverage A) atTop
      (nhds (∫ s in (0 : ℝ)..1, Averages.sineWeight s • A s)) := by
  have hwc : Continuous Averages.sineWeight := by
    unfold Averages.sineWeight
    fun_prop
  have hw0 : Averages.sineWeight 0 = 0 := by simp [Averages.sineWeight]
  have hd : Tendsto (interiorMean Averages.sineWeight) atTop (nhds 1) := by
    simpa only [Averages.integral_sineWeight] using
      interiorMean_tendsto (by positivity : 0 ≤ 2 * Real.pi) hwc hw0 sineWeight_lipschitz
  have hn := interiorMean_tendsto hL hc (by simp only [hw0, zero_smul]) hLip
  have hquot := (hd.inv₀ one_ne_zero).smul hn
  simp only [inv_one, one_smul] at hquot
  apply hquot.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact (modeAverage_eq_ratio A hN).symm

end

end PositiveEinsteinFour.Jacobi

end OAI
