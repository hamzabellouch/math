import OAI.NumberTheory.CubicMoment.Estimates.TripleScaleSpread

namespace OAI

/-! A product envelope fixes the sum of the three smooth norm indices
up to an absolute interval. Its location may grow with X; its length
is independent of X. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma tripleNormScale_log_product (k : Fin 3 → ℕ) :
    Real.log (∏ i, tripleNormScale k i) =
      ((∑ i, k i):ℕ)*Real.log (4/3:ℝ)-3*Real.log 2 := by
  rw [Real.log_prod (fun i _ => (tripleNormScale_pos k i).ne')]
  have he (i : Fin 3) : Real.log (tripleNormScale k i) =
      (k i:ℝ)*Real.log (4/3:ℝ)-Real.log 2 := by
    rw [tripleNormScale,Real.log_div (pow_pos (by norm_num : (0:ℝ) < 4/3) _).ne'
      (by norm_num),Real.log_pow]
  simp_rw [he]
  rw [Finset.sum_sub_distrib,←Finset.sum_mul]
  simp

def tripleIndexEnvelopeWidth : ℕ := ⌈20/Real.log (4/3:ℝ)⌉₊+1

def tripleIndexEnvelopeStart (X : ℝ) : ℕ :=
  ⌊Real.log X/Real.log (4/3:ℝ)⌋₊-tripleIndexEnvelopeWidth

lemma tripleNormScale_index_sum_range {X : ℝ} (hX : 1 ≤ X) (k : Fin 3 → ℕ)
    (hlo : X/16 ≤ ∏ i, tripleNormScale k i) (hhi : (∏ i, tripleNormScale k i) ≤ 3*X) :
    tripleIndexEnvelopeStart X ≤ ∑ i, k i ∧
      (∑ i, k i) ≤ tripleIndexEnvelopeStart X+(2*tripleIndexEnvelopeWidth+1) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hr : 0 < Real.log (4/3:ℝ) := Real.log_pos (by norm_num)
  have hl := Real.log_le_log (by positivity : (0:ℝ) < X/16) hlo
  have hu := Real.log_le_log (Finset.prod_pos (fun i _ => tripleNormScale_pos k i)) hhi
  rw [Real.log_div hXp.ne' (by norm_num),tripleNormScale_log_product] at hl
  rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hXp.ne',tripleNormScale_log_product] at hu
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hu2 : Real.log 2 ≤ 2 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)).trans (by norm_num)
  have hu3 : Real.log 3 ≤ 3 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)).trans (by norm_num)
  have hu16 : Real.log 16 ≤ 16 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 16)).trans (by norm_num)
  have hsumlo : Real.log X/Real.log (4/3:ℝ) - 20/Real.log (4/3:ℝ) ≤ ((∑ i, k i):ℕ) := by
    rw [←sub_div]
    apply (div_le_iff₀ hr).mpr
    nlinarith
  have hsumhi : (((∑ i, k i):ℕ):ℝ) ≤ Real.log X/Real.log (4/3:ℝ)+20/Real.log (4/3:ℝ) := by
    rw [←add_div]
    apply (le_div_iff₀ hr).mpr
    nlinarith
  let N := ⌊Real.log X/Real.log (4/3:ℝ)⌋₊
  have hfloor : (N:ℝ) ≤ Real.log X/Real.log (4/3:ℝ) := Nat.floor_le (div_nonneg (Real.log_nonneg hX) hr.le)
  have hfloor' : Real.log X/Real.log (4/3:ℝ) < (N:ℝ)+1 := Nat.lt_floor_add_one _
  have hJ : 20/Real.log (4/3:ℝ) ≤ (tripleIndexEnvelopeWidth:ℝ) := by
    have hh := Nat.le_ceil (20/Real.log (4/3:ℝ))
    dsimp only [tripleIndexEnvelopeWidth]
    push_cast
    linarith
  have hlow : N ≤ (∑ i, k i)+tripleIndexEnvelopeWidth := by
    exact_mod_cast (show (N:ℝ) ≤ ((∑ i, k i):ℕ)+(tripleIndexEnvelopeWidth:ℝ) by linarith)
  have hhigh : (∑ i, k i) ≤ N+tripleIndexEnvelopeWidth+1 := by
    exact_mod_cast (show (((∑ i, k i):ℕ):ℝ) ≤ (N:ℝ)+(tripleIndexEnvelopeWidth:ℝ)+1 by linarith)
  change N-tripleIndexEnvelopeWidth ≤ _ ∧ _ ≤ N-tripleIndexEnvelopeWidth+(2*tripleIndexEnvelopeWidth+1)
  omega

end CubicFirstMoment

end

end OAI
