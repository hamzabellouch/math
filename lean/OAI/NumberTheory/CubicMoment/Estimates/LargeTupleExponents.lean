import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleSupport
import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupingGap

namespace OAI

/-! Normalized logarithmic prime sizes in the actual large-row support.
They form a positive partition of one uniformly away from two thirds. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

def largePrimeTupleProduct {i j : ℕ}
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) : Eisenstein :=
  (∏ a, q.1 a)*(∏ b, q.2 b)

def largePrimeTupleExponent {i j : ℕ}
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) (a : Fin i ⊕ Fin j) : ℝ :=
  Real.log (largePrimeTupleNorm q a)/Real.log (norm (largePrimeTupleProduct q))

lemma largePrimeTupleNorm_prod {i j : ℕ}
    (q : (Fin i → Eisenstein) × (Fin j → Eisenstein)) :
    (∏ a, largePrimeTupleNorm q a) = norm (largePrimeTupleProduct q) := by
  rw [Fintype.prod_sum_type]
  simp only [largePrimeTupleNorm,Sum.elim_inl,Sum.elim_inr,largePrimeTupleProduct,
    norm_mul_eq,norm_finset_prod]

lemma largePrimeTupleExponent_sum {i j : ℕ} {X : ℝ}
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hn : Real.log (norm (largePrimeTupleProduct q)) ≠ 0) :
    (∑ a, largePrimeTupleExponent q a) = 1 := by
  unfold largePrimeTupleExponent
  rw [←Finset.sum_div,←Real.log_prod]
  · rw [largePrimeTupleNorm_prod,div_self hn]
  · intro a _ha
    exact ne_of_gt (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq a).1)

lemma largePrimeTupleExponent_bounds {i j : ℕ} {ℓ : ℤ} {ξ : ℝ}
    {Ct : ℕ} {H X : ℝ} (hX : 1 ≤ X) (hlog : 200 ≤ Real.log X)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    {q : (Fin i → Eisenstein) × (Fin j → Eisenstein)}
    (hq : q ∈ largePrimeTupleBox i j X)
    (hne : largePrimeTupleTerm i j ℓ ξ Ct H X q ≠ 0) (a : Fin i ⊕ Fin j) :
    ξ/2 ≤ largePrimeTupleExponent q a ∧ largePrimeTupleExponent q a ≤ 13/20 := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hnrange := largePrimeTupleTerm_product_range hXp hne
  change X/2 ≤ norm (largePrimeTupleProduct q) ∧
    norm (largePrimeTupleProduct q) ≤ 3*X at hnrange
  have hnp : 0 < norm (largePrimeTupleProduct q) := (by positivity : (0:ℝ) < X/2).trans_le hnrange.1
  have hlower := Real.log_le_log (by positivity : (0:ℝ) < X/2) hnrange.1
  rw [Real.log_div hXp.ne' (by norm_num)] at hlower
  have hupper := Real.log_le_log hnp hnrange.2
  rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hXp.ne'] at hupper
  have hlog2 : Real.log 2 ≤ 2 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)).trans (by norm_num)
  have hlog3 : Real.log 3 ≤ 3 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)).trans (by norm_num)
  have hlogn : 0 < Real.log (norm (largePrimeTupleProduct q)) := by linarith
  have hlogsmall := Real.log_le_log (Real.rpow_pos_of_pos hXp ξ)
    (largePrimeTupleNorm_rough_bound hX hξz hq hne a).le
  rw [Real.log_rpow hXp] at hlogsmall
  have hloglarge := Real.log_le_log
    (zero_lt_one.trans_le (largePrimeTupleNorm_bounds hq a).1)
    (largePrimeTupleNorm_upper_bound hX hξz hq hne a)
  rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0)
    (Real.rpow_pos_of_pos hXp (31/50:ℝ)).ne',Real.log_rpow hXp] at hloglarge
  unfold largePrimeTupleExponent
  constructor
  · apply (le_div_iff₀ hlogn).mpr
    have hntwo : Real.log (norm (largePrimeTupleProduct q)) ≤ 2*Real.log X := by linarith
    nlinarith
  · apply (div_le_iff₀ hlogn).mpr
    linarith

end CubicFirstMoment

end

end OAI
