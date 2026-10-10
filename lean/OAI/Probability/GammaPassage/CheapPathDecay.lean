import OAI.Probability.GammaPassage.CheapPathCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP
open scoped ENNReal

noncomputable def cheapChernoff (shape rate : ℝ) : ℝ :=
  rate * (Real.exp (Real.log 16 / shape) - 1)

noncomputable def cheapSlope (shape rate : ℝ) : ℝ :=
  Real.log 2 / cheapChernoff shape rate

lemma cheapChernoff_pos {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    0 < cheapChernoff shape rate := by
  have hl : 0 < Real.log (16 : ℝ) := Real.log_pos (by norm_num)
  exact mul_pos hr (sub_pos.mpr (Real.one_lt_exp_iff.mpr (div_pos hl hs)))

lemma cheapSlope_pos {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    0 < cheapSlope shape rate :=
  div_pos (Real.log_pos (by norm_num)) (cheapChernoff_pos hs hr)

/-- The exact native Gamma Laplace factor is 1/16 at the chosen parameter. -/
lemma cheapChernoff_factor {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    (rate / (rate + cheapChernoff shape rate)) ^ shape = (1 / 16 : ℝ) := by
  have hd : rate + cheapChernoff shape rate =
      rate * Real.exp (Real.log 16 / shape) := by
    unfold cheapChernoff
    ring
  have hratio : rate / (rate + cheapChernoff shape rate) =
      Real.exp (-(Real.log 16 / shape)) := by
    rw [hd, Real.exp_neg]
    field_simp [hr.ne', Real.exp_ne_zero]
  rw [hratio, ← Real.exp_mul]
  have he : -(Real.log 16 / shape) * shape = -Real.log 16 := by
    field_simp [hs.ne']
  rw [he, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
  norm_num

lemma cheapChernoff_mul_slope {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    cheapChernoff shape rate * cheapSlope shape rate = Real.log 2 := by
  unfold cheapSlope
  field_simp [(cheapChernoff_pos hs hr).ne']

/-- Exact cancellation of counting, Laplace factor and linear threshold. -/
lemma cheap_count_bound_eq {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) (n : ℕ) :
    (4 : ℝ)^n * (((rate / (rate + cheapChernoff shape rate)) ^ shape)^n /
      Real.exp (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)))) =
        (1 / 2 : ℝ)^n := by
  rw [cheapChernoff_factor hs hr]
  have he : -cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)) =
      (n : ℝ) * (-Real.log 2) := by
    have hc := cheapChernoff_mul_slope hs hr
    calc
      _ = -(cheapChernoff shape rate * cheapSlope shape rate) * (n : ℝ) := by ring
      _ = _ := by rw [hc]; ring
  rw [he, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [← div_pow, ← mul_pow]
  norm_num

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- All actual trails of n steps from p are exponentially unlikely to cost at
most c*n. This includes n=0, where the empty path has probability one. -/
theorem GammaEnvironment.cheap_fixed_length_decay_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (n : ℕ) :
    P.real {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧
        pathCost (fun e => τ e ω) p ds ≤ cheapSlope shape rate * (n : ℝ)} ≤
      (1 / 2 : ℝ)^n := by
  have hsp := cheapChernoff_pos hs hr
  have hbase : 0 ≤ (rate / (rate + cheapChernoff shape rate)) ^ shape :=
    (Real.rpow_pos_of_pos (div_pos hr (add_pos hr hsp)) shape).le
  have hden : ENNReal.ofReal (Real.exp
      (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)))) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hfin : ((4 ^ n : ℕ) : ℝ≥0∞) *
      ((ENNReal.ofReal ((rate / (rate + cheapChernoff shape rate)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp
          (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ))))) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp)
      (ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hden)
  have hb := ENNReal.toReal_mono hfin
    (h.cheap_fixed_length_probability hs hr (cheapChernoff shape rate) hsp p n
      (cheapSlope shape rate * (n : ℝ)))
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hbase,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, Nat.cast_pow, Nat.cast_ofNat] at hb
  change P.real _ ≤ _ at hb
  rw [cheap_count_bound_eq hs hr n] at hb
  exact hb

end GammaFPP

end OAI
