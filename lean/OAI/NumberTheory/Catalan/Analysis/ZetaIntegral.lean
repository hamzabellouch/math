import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import OAI.NumberTheory.Catalan.Analysis.LogMonomial
import OAI.NumberTheory.Catalan.Determinants.RealColumnDeterminant
import OAI.NumberTheory.Catalan.Estimates.Contract

namespace OAI

noncomputable section

namespace InternalCatalan

section

open Filter
open scoped BigOperators Topology

def zetaTerm (i j u : ℕ) : ℝ :=
  1 / (((i + u + 1 : ℕ) : ℝ) * ((j + u + 1 : ℕ) : ℝ))

def zetaSeries (i j : ℕ) : ℝ := ∑' u : ℕ, zetaTerm i j u

theorem zetaTerm_nonneg (i j u : ℕ) : 0 ≤ zetaTerm i j u := by
  unfold zetaTerm
  positivity

theorem zetaTerm_le_inverse_square (i j u : ℕ) :
    zetaTerm i j u ≤ 1 / ((u + 1 : ℕ) : ℝ) ^ 2 := by
  unfold zetaTerm
  apply one_div_le_one_div_of_le (by positivity)
  have hi : ((u + 1 : ℕ) : ℝ) ≤ ((i + u + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show u + 1 ≤ i + u + 1 by omega)
  have hj : ((u + 1 : ℕ) : ℝ) ≤ ((j + u + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show u + 1 ≤ j + u + 1 by omega)
  simpa only [pow_two] using
    mul_le_mul hi hj (by positivity) (by positivity)

theorem summable_inverse_square_succ :
    Summable (fun u : ℕ => 1 / ((u + 1 : ℕ) : ℝ) ^ 2) := by
  have h : Summable (fun u : ℕ => 1 / (u : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)
  exact h.comp_injective (show Function.Injective (fun u : ℕ => u + 1) by
    intro a b hab
    change a + 1 = b + 1 at hab
    omega)

theorem summable_zetaTerm (i j : ℕ) : Summable (zetaTerm i j) := by
  apply summable_inverse_square_succ.of_norm_bounded
  intro u
  rw [Real.norm_eq_abs, abs_of_nonneg (zetaTerm_nonneg i j u)]
  exact zetaTerm_le_inverse_square i j u

theorem summable_norm_zetaTerm (i j : ℕ) :
    Summable (fun u : ℕ => ‖zetaTerm i j u‖) := by
  simpa only [Real.norm_eq_abs, abs_of_nonneg (zetaTerm_nonneg i j _)] using
    summable_zetaTerm i j

theorem hasSum_zetaSeries (i j : ℕ) : HasSum (zetaTerm i j) (zetaSeries i j) :=
  (summable_zetaTerm i j).hasSum

theorem tendsto_partial_sums_zetaSeries (i j : ℕ) :
    Tendsto (fun m : ℕ => ∑ u ∈ Finset.range m, zetaTerm i j u)
      atTop (𝓝 (zetaSeries i j)) :=
  (hasSum_zetaSeries i j).tendsto_sum_nat

theorem zetaSeries_nonneg (i j : ℕ) : 0 ≤ zetaSeries i j :=
  tsum_nonneg (zetaTerm_nonneg i j)

theorem zetaSeries_symm (i j : ℕ) : zetaSeries i j = zetaSeries j i := by
  apply tsum_congr
  intro u
  simp only [zetaTerm, mul_comm]

theorem zetaTerm_shift (i j u m : ℕ) :
    zetaTerm i j (u + m) = zetaTerm (i + m) (j + m) u := by
  simp only [zetaTerm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem zetaSeries_split (i j m : ℕ) :
    (∑ u ∈ Finset.range m, zetaTerm i j u) + zetaSeries (i + m) (j + m) =
      zetaSeries i j := by
  have h := (summable_zetaTerm i j).sum_add_tsum_nat_add m
  simpa only [zetaTerm_shift, zetaSeries] using h

theorem zetaSeries_step (i j : ℕ) :
    zetaSeries i j - zetaSeries (i + 1) (j + 1) =
      1 / (((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) := by
  have h := zetaSeries_split i j 1
  simp only [Finset.sum_range_one, zetaTerm, Nat.add_zero] at h
  linarith

theorem tendsto_zetaSeries_diagonal_tail (i j : ℕ) :
    Tendsto (fun m : ℕ => zetaSeries (i + m) (j + m)) atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add (zetaTerm i j)
  simpa only [zetaTerm_shift, zetaSeries] using h

theorem zetaSeries_zero_zero :
    zetaSeries 0 0 = ∑' u : ℕ, 1 / ((u + 1 : ℕ) : ℝ) ^ 2 := by
  simp only [zetaSeries, zetaTerm, Nat.zero_add, pow_two]

theorem zetaSeries_diagonal (i : ℕ) :
    zetaSeries i i = (zetaRat i i : ℝ) + zetaSeries 0 0 := by
  have h := zetaSeries_split 0 0 i
  have hs : (∑ u ∈ Finset.range i, zetaTerm 0 0 u) = (harmonicRat 2 i : ℝ) := by
    simp [zetaTerm, harmonicRat, pow_two]
  rw [hs] at h
  simp only [Nat.zero_add] at h
  rw [zetaRat_diagonal, Rat.cast_neg]
  linarith

end

section

open Filter
open scoped Topology

theorem summable_odd_reciprocal_squares :
    Summable (fun j : ℕ => 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2) := by
  have h : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)
  exact h.comp_injective (show Function.Injective (fun j : ℕ => 2 * j + 1) by
    intro i j hij
    change 2 * i + 1 = 2 * j + 1 at hij
    omega)

theorem norm_catalan_summand (j : ℕ) :
    ‖(-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2‖ =
      1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by
  simp only [norm_div, norm_pow, norm_neg, norm_one, one_pow, Real.norm_natCast]

theorem summable_norm_catalan_summand :
    Summable (fun j : ℕ => ‖(-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2‖) := by
  simpa only [norm_catalan_summand] using summable_odd_reciprocal_squares

theorem summable_catalan_summand :
    Summable (fun j : ℕ => (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) := by
  exact summable_odd_reciprocal_squares.of_norm_bounded
    (fun j => (norm_catalan_summand j).le)

theorem hasSum_catalan :
    HasSum (fun j : ℕ => (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) catalan := by
  exact summable_catalan_summand.hasSum

theorem tendsto_partial_sums_catalan :
    Tendsto
      (fun m : ℕ => ∑ j ∈ Finset.range m,
        (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      atTop (𝓝 catalan) := by
  exact hasSum_catalan.tendsto_sum_nat

end

section

open MeasureTheory
open scoped BigOperators Topology

theorem hasSum_zetaKernel (i j : ℕ) {t s : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    HasSum (fun u : ℕ => t ^ (i + u) * s ^ (j + u))
      (t ^ i * s ^ j / (1 - t * s)) := by
  have hts : |t * s| < 1 := by
    rw [abs_of_nonneg (mul_nonneg ht.1.le hs.1.le)]
    have hmul : t * s < t := by nlinarith [ht.1, hs.2]
    exact hmul.trans ht.2
  convert (hasSum_geometric_of_abs_lt_one hts).mul_left (t ^ i * s ^ j) using 1
  · ext u
    simp only [pow_add, mul_pow]
    ring
  · rfl

theorem integrableOn_pow_unit (k : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ k) (Set.Ioo (0 : ℝ) 1) := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
  exact (continuous_id.pow k).intervalIntegrable 0 1

theorem integrable_zetaMonomial (i j u : ℕ) :
    Integrable (fun p : ℝ × ℝ => p.1 ^ (i + u) * p.2 ^ (j + u))
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Set.Ioo (0 : ℝ) 1))) :=
  (integrableOn_pow_unit (i + u)).mul_prod (integrableOn_pow_unit (j + u))

theorem integral_zetaMonomial (i j u : ℕ) :
    (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1,
      t ^ (i + u) * s ^ (j + u)) = zetaTerm i j u := by
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
    integral_pow, one_pow, zero_pow (Nat.add_one_ne_zero _),
    sub_zero, zetaTerm, Nat.cast_add, Nat.cast_one]
  simp only [one_div, mul_inv_rev]
  ring

end

section

open MeasureTheory Set
open scoped BigOperators Topology

theorem hasSum_catalanLogKernel {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (x ^ (2 * n) * (-Real.log x)))
      (-Real.log x / (1 + x ^ 2)) := by
  have hsq : |(-1 : ℝ) * x ^ 2| < 1 := by
    rw [abs_mul, abs_neg, abs_one, one_mul, abs_of_nonneg (sq_nonneg x)]
    nlinarith [hx.1, hx.2]
  convert (hasSum_geometric_of_abs_lt_one hsq).mul_left (-Real.log x) using 1
  · ext n
    rw [mul_pow, ← pow_mul]
    ring
  · simp only [neg_one_mul, sub_neg_eq_add, div_eq_mul_inv]

theorem intervalIntegrable_catalanLogKernel :
    IntervalIntegrable (fun x : ℝ => -Real.log x / (1 + x ^ 2)) volume 0 1 := by
  have hc : Continuous (fun x : ℝ => 1 / (1 + x ^ 2)) :=
    continuous_const.div (continuous_const.add (continuous_id.pow 2))
      (fun x => by positivity)
  simpa only [mul_one_div, Pi.neg_apply] using
    (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1)).neg.mul_continuousOn
      hc.continuousOn

theorem integrableOn_catalanLogKernel :
    IntegrableOn (fun x : ℝ => -Real.log x / (1 + x ^ 2)) (Ioo (0 : ℝ) 1) := by
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    intervalIntegrable_catalanLogKernel

theorem integral_Ioo_catalanLogKernel :
    (∫ x : ℝ in Ioo (0 : ℝ) 1, -Real.log x / (1 + x ^ 2)) = catalan := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  let F : ℕ → ℝ → ℝ := fun n x => (-1 : ℝ) ^ n * (x ^ (2 * n) * (-Real.log x))
  have hF (n : ℕ) : Integrable (F n) μ := by
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp
        (intervalIntegrable_pow_neg_log (2 * n))).const_mul ((-1 : ℝ) ^ n)
  have hbase (n : ℕ) :
      (∫ x : ℝ, x ^ (2 * n) * (-Real.log x) ∂μ) =
        1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
    simpa only [μ, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
      integral_Ioc_eq_integral_Ioo] using integral_pow_neg_log (2 * n)
  have hterm (n : ℕ) : (∫ x, F n x ∂μ) =
      (-1 : ℝ) ^ n / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
    change (∫ x : ℝ, (-1 : ℝ) ^ n * (x ^ (2 * n) * (-Real.log x)) ∂μ) = _
    rw [integral_const_mul, hbase]
    ring
  have hnorm (n : ℕ) : (∫ x, ‖F n x‖ ∂μ) =
      1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [← hbase n]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    dsimp only [F]
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact Real.norm_of_nonneg (mul_nonneg (pow_nonneg hx.1.le _)
      (neg_nonneg.mpr (Real.log_nonpos hx.1.le hx.2.le)))
  have hsum : Summable (fun n => ∫ x, ‖F n x‖ ∂μ) := by
    simpa only [hnorm] using summable_odd_reciprocal_squares
  have hgeom : (fun x => ∑' n, F n x) =ᵐ[μ]
      (fun x : ℝ => -Real.log x / (1 + x ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hasSum_catalanLogKernel hx).tsum_eq
  calc
    (∫ x : ℝ, -Real.log x / (1 + x ^ 2) ∂μ) =
        ∫ x, (∑' n, F n x) ∂μ := integral_congr_ae hgeom.symm
    _ = ∑' n, ∫ x, F n x ∂μ :=
      (integral_tsum_of_summable_integral_norm hF hsum).symm
    _ = catalan := by simp only [hterm, catalan]

theorem integral_catalanLogKernel :
    (∫ x in (0 : ℝ)..1, -Real.log x / (1 + x ^ 2)) = catalan := by
  simpa only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] using integral_Ioo_catalanLogKernel

theorem hasSum_reciprocal_squares_zetaSeries :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (zetaSeries 0 0) := by
  have hbase := hasSum_zetaSeries 0 0
  change HasSum (fun n : ℕ =>
    1 / (((0 + n + 1 : ℕ) : ℝ) * ((0 + n + 1 : ℕ) : ℝ)))
      (zetaSeries 0 0) at hbase
  have htail : HasSum (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2)
      (zetaSeries 0 0) := by
    simpa only [Nat.zero_add, pow_two] using hbase
  have h := HasSum.zero_add (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) htail
  simpa only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), div_zero, zero_add]
    using h

theorem hasSum_even_reciprocal_squares :
    HasSum (fun n : ℕ => 1 / ((2 * n : ℕ) : ℝ) ^ 2)
      ((1 / 4 : ℝ) * zetaSeries 0 0) := by
  convert hasSum_reciprocal_squares_zetaSeries.mul_left (1 / 4 : ℝ) using 1
  ext n
  simp only [Nat.cast_mul, Nat.cast_ofNat, mul_pow, one_div, mul_inv_rev]
  norm_num
  ring

theorem tsum_odd_reciprocal_squares :
    (∑' n : ℕ, 1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2) =
      (3 / 4 : ℝ) * zetaSeries 0 0 := by
  have h := hasSum_reciprocal_squares_zetaSeries.unique
    (HasSum.even_add_odd (f := fun n : ℕ => 1 / (n : ℝ) ^ 2)
      hasSum_even_reciprocal_squares summable_odd_reciprocal_squares.hasSum)
  linarith

theorem hasSum_oddLogKernel {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun n : ℕ => x ^ (2 * n) * (-Real.log x))
      (-Real.log x / (1 - x ^ 2)) := by
  have hsq : |x ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg x)]
    nlinarith [hx.1, hx.2]
  convert (hasSum_geometric_of_abs_lt_one hsq).mul_left (-Real.log x) using 1
  · ext n
    rw [← pow_mul]
    ring
  · rfl

theorem integral_Ioo_oddLogKernel :
    (∫ x : ℝ in Ioo (0 : ℝ) 1, -Real.log x / (1 - x ^ 2)) =
      (3 / 4 : ℝ) * zetaSeries 0 0 := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  let F : ℕ → ℝ → ℝ := fun n x => x ^ (2 * n) * (-Real.log x)
  have hF (n : ℕ) : Integrable (F n) μ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp (intervalIntegrable_pow_neg_log (2 * n))
  have hterm (n : ℕ) : (∫ x, F n x ∂μ) =
      1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
    simpa only [μ, F, intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ 1 by norm_num), integral_Ioc_eq_integral_Ioo]
      using integral_pow_neg_log (2 * n)
  have hnorm (n : ℕ) : (∫ x, ‖F n x‖ ∂μ) =
      1 / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [← hterm n]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact Real.norm_of_nonneg (mul_nonneg (pow_nonneg hx.1.le _)
      (neg_nonneg.mpr (Real.log_nonpos hx.1.le hx.2.le)))
  have hsum : Summable (fun n => ∫ x, ‖F n x‖ ∂μ) := by
    simpa only [hnorm] using summable_odd_reciprocal_squares
  have hgeom : (fun x => ∑' n, F n x) =ᵐ[μ]
      (fun x : ℝ => -Real.log x / (1 - x ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hasSum_oddLogKernel hx).tsum_eq
  calc
    (∫ x : ℝ, -Real.log x / (1 - x ^ 2) ∂μ) =
        ∫ x, (∑' n, F n x) ∂μ := integral_congr_ae hgeom.symm
    _ = ∑' n, ∫ x, F n x ∂μ :=
      (integral_tsum_of_summable_integral_norm hF hsum).symm
    _ = (3 / 4 : ℝ) * zetaSeries 0 0 := by
      simpa only [hterm] using tsum_odd_reciprocal_squares

theorem integral_two_oddLogKernel :
    (∫ x in (0 : ℝ)..1, -2 * Real.log x / (1 - x ^ 2)) =
      (3 / 2 : ℝ) * zetaSeries 0 0 := by
  have h : (∫ x in (0 : ℝ)..1, -Real.log x / (1 - x ^ 2)) =
      (3 / 4 : ℝ) * zetaSeries 0 0 := by
    simpa only [intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ 1 by norm_num), integral_Ioc_eq_integral_Ioo]
      using integral_Ioo_oddLogKernel
  calc
    _ = 2 * ∫ x in (0 : ℝ)..1, -Real.log x / (1 - x ^ 2) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = _ := by rw [h]; ring

end

open MeasureTheory Set Polynomial
open scoped BigOperators Topology

private theorem ae_mem_unit_square :
    ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1)),
      p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioo.prod measurableSet_Ioo)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact ⟨ht, hs⟩

theorem integral_prod_zetaKernel (i j : ℕ) :
    (∫ p : ℝ × ℝ, p.1 ^ i * p.2 ^ j / (1 - p.1 * p.2)
      ∂(volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) = zetaSeries i j := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  let F : ℕ → ℝ × ℝ → ℝ := fun u p => p.1 ^ (i + u) * p.2 ^ (j + u)
  have hF : ∀ u, Integrable (F u) (μ.prod μ) := fun u =>
    integrable_zetaMonomial i j u
  have hterm (u : ℕ) : (∫ p, F u p ∂μ.prod μ) = zetaTerm i j u := by
    rw [integral_prod _ (hF u)]
    simpa only [μ, F, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
      integral_Ioc_eq_integral_Ioo] using integral_zetaMonomial i j u
  have hnorm (u : ℕ) : (∫ p, ‖F u p‖ ∂μ.prod μ) = zetaTerm i j u := by
    rw [← hterm u]
    apply integral_congr_ae
    filter_upwards [ae_mem_unit_square] with p hp
    exact Real.norm_of_nonneg
      (mul_nonneg (pow_nonneg hp.1.1.le _) (pow_nonneg hp.2.1.le _))
  have hsum : Summable (fun u => ∫ p, ‖F u p‖ ∂μ.prod μ) := by
    simpa only [hnorm] using summable_zetaTerm i j
  have hinterchange := integral_tsum_of_summable_integral_norm hF hsum
  have hgeom : (fun p => ∑' u, F u p) =ᵐ[μ.prod μ]
      (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j / (1 - p.1 * p.2)) := by
    filter_upwards [ae_mem_unit_square] with p hp
    exact (hasSum_zetaKernel i j hp.1 hp.2).tsum_eq
  calc
    (∫ p : ℝ × ℝ, p.1 ^ i * p.2 ^ j / (1 - p.1 * p.2) ∂μ.prod μ) =
        ∫ p, (∑' u, F u p) ∂μ.prod μ := integral_congr_ae hgeom.symm
    _ = ∑' u, ∫ p, F u p ∂μ.prod μ := hinterchange.symm
    _ = zetaSeries i j := by simp only [hterm, zetaSeries]

theorem integrable_zetaKernel (i j : ℕ) :
    Integrable (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j / (1 - p.1 * p.2))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_prod_zetaKernel]
  have hstep := zetaSeries_step i j
  have htail := zetaSeries_nonneg (i + 1) (j + 1)
  have hzero : 0 < 1 / (((i + 1 : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ)) := by positivity
  have hpos : 0 < zetaSeries i j := by linarith
  exact hpos.ne'

theorem integral_zetaKernel (i j : ℕ) :
    (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1,
      t ^ i * s ^ j / (1 - t * s)) = zetaSeries i j := by
  have h := integral_prod
    (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j / (1 - p.1 * p.2))
    (integrable_zetaKernel i j)
  rw [integral_prod_zetaKernel] at h
  simpa only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] using h.symm

theorem zetaMoment_X_pow (i j : ℕ) :
    zetaMoment (X ^ i) (X ^ j) = zetaSeries i j := by
  simpa only [zetaMoment, Polynomial.eval_pow, Polynomial.eval_X] using
    integral_zetaKernel i j

end InternalCatalan

end

end OAI
