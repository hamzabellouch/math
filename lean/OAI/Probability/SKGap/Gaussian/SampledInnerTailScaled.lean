import Mathlib
import OAI.Probability.SKGap.Localization.BilinearCoefficient

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
namespace SKGapCutoff.RandomMatrix

lemma sampled_inner_tail_scaled (β : ℝ) (hβ : 0 < β) {n : ℕ} (hn : 0 < n)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    disorderLaw β n {g | 11*β ≤ |inner (𝕜 := ℝ)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g) x) y|} ≤
      2 * ENNReal.ofReal (Real.exp (-(10:ℝ)*n)) := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hcoef : ∑ p, bilinearCoefficient y x p ^ 2 ≤ 2 := by
    have hh := bilinearCoefficient_sq_le y x
    rw [← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq] at hh
    have hx2 : ‖x‖^2 ≤ 1 := by nlinarith [norm_nonneg x]
    have hy2 : ‖y‖^2 ≤ 1 := by nlinarith [norm_nonneg y]
    nlinarith [mul_le_mul hy2 hx2 (sq_nonneg ‖x‖) (by norm_num : (0:ℝ) ≤ 1)]
  simp_rw [sampled_inner]
  have hh := gaussian_linear_abs_tail (Real.toNNReal (β^2/n))
    (bilinearCoefficient y x) (11*β) (n/β) (div_pos hnR hβ)
  refine hh.trans (mul_le_mul' (le_refl 2) (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)))
  rw [Real.coe_toNNReal _ (div_nonneg (sq_nonneg β) hnR.le)]
  have hv : β^2/(n:ℝ) * (∑ p, bilinearCoefficient y x p^2) * (n/β)^2 / 2 ≤ n := by
    calc
      _ ≤ β^2/(n:ℝ) * 2 * (n/β)^2 / 2 := by gcongr
      _ = _ := by field_simp
  have he : (n:ℝ)/β*(11*β)=11*n := by field_simp
  rw [he]
  linarith

lemma sampled_opNorm_tail_scaled (β : ℝ) (hβ : 0 < β) {n : ℕ} (hn : 0 < n) :
    disorderLaw β n {g | 2*(11*β) < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g)‖} ≤
      ENNReal.ofReal (2 * (81:ℝ)^n * Real.exp (-(10:ℝ)*n)) := by
  classical
  obtain ⟨s, hb, hc, hs⟩ := unit_ball_net n
  let E (x y : EuclideanSpace ℝ (Fin n)) : Set (GaussianCoordinates n) :=
    {g | 11*β ≤ |inner (𝕜 := ℝ) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g) x) y|}
  have hsub : {g | 2*(11*β) < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g)‖} ⊆
      ⋃ x ∈ s, ⋃ y ∈ s, E x y := by
    intro g hg
    by_contra hnot
    have hb' : ∀ x ∈ s, ∀ y ∈ s, |inner (𝕜 := ℝ)
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g) x) y| ≤ 11*β := by
      intro x hx y hy
      have hh : g ∉ E x y := fun hgE => hnot (Set.mem_iUnion₂.mpr
        ⟨x, hx, Set.mem_iUnion₂.mpr ⟨y, hy, hgE⟩⟩)
      exact (not_le.mp hh).le
    have hh := opNorm_le_of_net (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g)) s hb hc
      (11*β) (by positivity) hb'
    exact not_lt_of_ge hh hg
  have hu : disorderLaw β n (⋃ x ∈ s, ⋃ y ∈ s, E x y) ≤
      ∑ x ∈ s, ∑ y ∈ s, disorderLaw β n (E x y) := by
    refine (measure_biUnion_finset_le s _).trans ?_
    exact Finset.sum_le_sum (fun x _ => measure_biUnion_finset_le s (E x))
  refine (measure_mono hsub).trans (hu.trans ?_)
  calc
    _ ≤ ∑ _x ∈ s, ∑ _y ∈ s, 2 * ENNReal.ofReal (Real.exp (-(10:ℝ)*n)) := by
      exact Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun y hy =>
        sampled_inner_tail_scaled β hβ hn x y (hb x hx) (hb y hy)))
    _ = ENNReal.ofReal (2 * (s.card:ℝ)^2 * Real.exp (-(10:ℝ)*n)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (show (0:ℝ) ≤ s.card by positivity), ENNReal.ofReal_natCast]
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have hh : (s.card : ℝ)^2 ≤ (81:ℝ)^n := by
        calc
          _ ≤ ((9:ℝ)^n)^2 := pow_le_pow_left₀ (by positivity) hs 2
          _ = _ := by rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num
      gcongr)

lemma sampled_opNorm_tendsto_scaled (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun n => disorderLaw β n {g |
      2*(11*β) < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g)‖})
      atTop (nhds 0) := by
  have hq : 81 * Real.exp (-10) < 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
    have h2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have hp : (81:ℝ) < (Real.exp 1)^10 := (by norm_num : (81:ℝ) < 2^10).trans_le
      (pow_le_pow_left₀ (by norm_num) h2 10)
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using hp
  have hlim : Tendsto (fun n : ℕ => 2 * (81:ℝ)^n * Real.exp (-(10:ℝ)*n))
      atTop (nhds 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by positivity : (0:ℝ) ≤ 81*Real.exp (-10)) hq).const_mul 2
    simp only [mul_zero] at hh
    convert! hh using 1
    ext n
    rw [mul_pow, ← Real.exp_nat_mul]
    rw [show (n:ℝ)*(-10) = -(10:ℝ)*n by ring]
    ring
  have hlimE : Tendsto (fun n : ℕ => ENNReal.ofReal
      (2 * (81:ℝ)^n * Real.exp (-(10:ℝ)*n))) atTop (nhds 0) := by
    convert! ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim using 1
    simp only [ENNReal.ofReal_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimE
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact sampled_opNorm_tail_scaled β hβ hn

end SKGapCutoff.RandomMatrix

end

end OAI
