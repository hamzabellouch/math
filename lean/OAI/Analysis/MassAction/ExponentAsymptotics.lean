import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace OAI

universe uAlpha uIota

/-! # Variable-exponent comparisons at a vanishing positive base

The affine-label construction uses exponent sequences rather than fixed
exponents. These lemmas justify comparison when the limiting exponents have a
strict gap, without replacing a variable power by the power of its limit.
-/

open Filter Asymptotics
open scoped Topology

namespace Problem326

variable {α : Type uAlpha} {l : Filter α} {h p q : α → ℝ} {a b : ℝ}

/-- A positive limiting exponent makes a power of a vanishing base vanish. -/
theorem tendsto_rpow_variable_zero
    (hh : Tendsto h l (𝓝 0)) (hp : Tendsto p l (𝓝 a)) (ha : 0 < a) :
    Tendsto (fun n => h n ^ p n) l (𝓝 0) := by
  simpa only [Real.zero_rpow ha.ne'] using hh.rpow hp (Or.inr ha)

/-- A strict limiting exponent gap gives a vanishing quotient of powers. -/
theorem tendsto_rpow_div_rpow_zero_of_gap
    (hpos : ∀ᶠ n in l, 0 < h n)
    (hh : Tendsto h l (𝓝 0))
    (hp : Tendsto p l (𝓝 a)) (hq : Tendsto q l (𝓝 b)) (hgap : b < a) :
    Tendsto (fun n => h n ^ p n / h n ^ q n) l (𝓝 0) := by
  have ht := tendsto_rpow_variable_zero hh (hp.sub hq) (sub_pos.mpr hgap)
  refine ht.congr' ?_
  filter_upwards [hpos] with n hn
  exact Real.rpow_sub hn (p n) (q n)

/-- Little-oh comparison remains valid for converging, variable exponents. -/
theorem isLittleO_rpow_variable_of_gap
    (hpos : ∀ᶠ n in l, 0 < h n)
    (hh : Tendsto h l (𝓝 0))
    (hp : Tendsto p l (𝓝 a)) (hq : Tendsto q l (𝓝 b)) (hgap : b < a) :
    (fun n => h n ^ p n) =o[l] (fun n => h n ^ q n) := by
  refine Asymptotics.isLittleO_of_tendsto' ?_
    (tendsto_rpow_div_rpow_zero_of_gap hpos hh hp hq hgap)
  filter_upwards [hpos] with n hn
  exact fun hz => False.elim ((Real.rpow_pos_of_pos hn (q n)).ne' hz)

/-- Reversing the strict limiting gap makes the quotient diverge to infinity. -/
theorem tendsto_rpow_div_rpow_atTop_of_gap
    (hpos : ∀ᶠ n in l, 0 < h n)
    (hh : Tendsto h l (𝓝 0))
    (hp : Tendsto p l (𝓝 a)) (hq : Tendsto q l (𝓝 b)) (hgap : a < b) :
    Tendsto (fun n => h n ^ p n / h n ^ q n) l atTop := by
  have hz := tendsto_rpow_div_rpow_zero_of_gap hpos hh hq hp hgap
  have hzpos : ∀ᶠ n in l, 0 < h n ^ q n / h n ^ p n := by
    filter_upwards [hpos] with n hn
    exact div_pos (Real.rpow_pos_of_pos hn _) (Real.rpow_pos_of_pos hn _)
  have ht := (tendsto_nhdsWithin_iff.mpr ⟨hz, hzpos⟩).inv_tendsto_nhdsGT_zero
  change Tendsto (fun n => (h n ^ q n / h n ^ p n)⁻¹) l atTop at ht
  simpa only [inv_div] using ht

/-- Eventual domination of powers forces the reverse order on limiting exponents. -/
theorem exponent_le_of_eventually_rpow_le [NeBot l]
    (hpos : ∀ᶠ n in l, 0 < h n)
    (hh : Tendsto h l (𝓝 0))
    (hp : Tendsto p l (𝓝 a)) (hq : Tendsto q l (𝓝 b))
    {C : ℝ} (hbound : ∀ᶠ n in l, h n ^ p n ≤ C * h n ^ q n) :
    b ≤ a := by
  by_contra hnot
  have hgap : a < b := lt_of_not_ge hnot
  have hlarge := (tendsto_rpow_div_rpow_atTop_of_gap hpos hh hp hq hgap).eventually
    (eventually_gt_atTop C)
  obtain ⟨n, hnpos, hnle, hnlt⟩ := (hpos.and (hbound.and hlarge)).exists
  have hden : 0 < h n ^ q n := Real.rpow_pos_of_pos hnpos _
  exact (not_lt_of_ge ((div_le_iff₀ hden).mpr hnle)) hnlt

/-- The big-oh version of the limiting exponent obstruction. -/
theorem exponent_le_of_isBigO_rpow [NeBot l]
    (hpos : ∀ᶠ n in l, 0 < h n)
    (hh : Tendsto h l (𝓝 0))
    (hp : Tendsto p l (𝓝 a)) (hq : Tendsto q l (𝓝 b))
    (hbound : (fun n => h n ^ p n) =O[l] (fun n => h n ^ q n)) :
    b ≤ a := by
  obtain ⟨C, hC⟩ := hbound.bound
  apply exponent_le_of_eventually_rpow_le hpos hh hp hq (C := C)
  filter_upwards [hpos, hC] with n hn hCn
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn _)] using hCn

/-- A positive leading power remains positive under a little-oh perturbation. -/
theorem eventually_pos_rpow_add_isLittleO {r : α → ℝ} {C : ℝ}
    (hpos : ∀ᶠ n in l, 0 < h n) (hC : 0 < C)
    (hr : r =o[l] (fun n => h n ^ q n)) :
    ∀ᶠ n in l, 0 < C * h n ^ q n + r n := by
  have he : ∀ᶠ n in l, -C < r n / h n ^ q n :=
    hr.tendsto_div_nhds_zero.eventually (lt_mem_nhds (neg_lt_zero.mpr hC))
  filter_upwards [hpos, he] with n hn hne
  have hden : 0 < h n ^ q n := Real.rpow_pos_of_pos hn _
  have hlt := (lt_div_iff₀ hden).mp hne
  linarith

/-- The corresponding negative leading term stays strictly negative. -/
theorem eventually_neg_neg_rpow_add_isLittleO {r : α → ℝ} {C : ℝ}
    (hpos : ∀ᶠ n in l, 0 < h n) (hC : 0 < C)
    (hr : r =o[l] (fun n => h n ^ q n)) :
    ∀ᶠ n in l, -C * h n ^ q n + r n < 0 := by
  have he := eventually_pos_rpow_add_isLittleO hpos hC hr.neg_left
  filter_upwards [he] with n hn
  linarith

/-- A finite linear combination of powers with larger limiting exponents is
little-oh of the comparison power. Coefficients need not be positive. -/
theorem isLittleO_sum_mul_rpow_variable_of_gap {ι : Type uIota}
    (s : Finset ι) (c : ι → ℝ) {p : α → ι → ℝ} {a : ι → ℝ}
    (hpos : ∀ᶠ n in l, 0 < h n) (hh : Tendsto h l (𝓝 0))
    (hp : ∀ i ∈ s, Tendsto (fun n => p n i) l (𝓝 (a i)))
    (hq : Tendsto q l (𝓝 b)) (hgap : ∀ i ∈ s, b < a i) :
    (fun n => ∑ i ∈ s, c i * h n ^ p n i) =o[l] (fun n => h n ^ q n) := by
  exact Asymptotics.IsLittleO.fun_sum fun i hi =>
    (isLittleO_rpow_variable_of_gap hpos hh (hp i hi) hq (hgap i hi)).const_mul_left (c i)

end Problem326

end OAI
