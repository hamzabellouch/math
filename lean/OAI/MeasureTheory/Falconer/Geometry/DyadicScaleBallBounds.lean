import OAI.MeasureTheory.Falconer.Recursion.FrostmanProfiles

namespace OAI

/-! # The finite-scale ball hypothesis supplies all required dyadic cell bounds -/

namespace Falconer.Regularization
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem dyadic_scale_ball_extension (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (N : ℕ) {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 ≤ s)
    (hball : ∀ x : Space d, ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
      μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^s))
    (x : Space d) {r : ℝ} (hr : ((2:ℝ)^N)⁻¹ ≤ r) :
    μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^s) := by
  by_cases hr1 : r ≤ 1
  · exact hball x r hr hr1
  have h1 : 1 ≤ ((2:ℝ)^N)^ε := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hε
  have h2 : 1 ≤ r^s := Real.one_le_rpow (le_of_not_ge hr1) hs
  calc
    _ ≤ 1 := prob_le_one
    _ = ENNReal.ofReal (1:ℝ) := by simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith)

theorem dyadic_scale_cell_bound (hd : 0 < d) (Q : DyadicCube d) (hQ : Q.side = 1)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N) {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 ≤ s)
    (hball : ∀ x : Space d, ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
      μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^s))
    {a : ℕ} (ha : a ≤ N) (p : CellPath d) (hp : p.length = a) :
    (μ (Q.descendant p).carrier).toReal ≤
      (2*Real.sqrt d)^s*((2:ℝ)^N)^ε*((2:ℝ)^N)^(-s*(a:ℝ)/(N:ℝ)) := by
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have hsqrt : 1 ≤ Real.sqrt (d:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  have hlow : ((2:ℝ)^N)⁻¹ ≤ 2*Real.sqrt d*(Q.descendant p).side := by
    rw [Q.descendant_side,hQ,hp]
    have hpow : ((2:ℝ)^N)⁻¹ ≤ ((2:ℝ)^a)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) ha)
    have hc : (1:ℝ) ≤ 2*Real.sqrt d := by linarith
    exact hpow.trans (by simpa only [one_div,one_mul] using
      mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr (by positivity : (0:ℝ) ≤ 2^a)))
  have hmeasure : μ (Q.descendant p).carrier ≤
      ENNReal.ofReal (((2:ℝ)^N)^ε*(2*Real.sqrt d*(Q.descendant p).side)^s) := by
    apply (measure_mono ?_).trans
      (dyadic_scale_ball_extension μ N hε hs hball (Q.descendant p).center hlow)
    intro z hz
    have hh := (Q.descendant p).dist_le (Q.descendant_side_pos hside p).le hz
      ((Q.descendant p).center_mem (Q.descendant_side_pos hside p))
    exact mem_ball.mpr (by nlinarith [Q.descendant_side_pos hside p])
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  have hsidep := Q.descendant_side_pos hside p
  rw [ENNReal.toReal_ofReal (by positivity)] at hh
  apply hh.trans_eq
  rw [Q.descendant_side,hQ,hp,show
    2*Real.sqrt d*(1/(2:ℝ)^a) = (2*Real.sqrt d)/(2:ℝ)^a by ring,
    Real.div_rpow (by positivity) (by positivity),dyadic_rpow_scale hN a s]
  ring

end Falconer.Regularization

end OAI
