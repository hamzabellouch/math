import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightCutoffDeriv

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
open scoped ContDiff
variable {ι : Type*}

def counterpartArchimedean (T U H u : ℝ) (S : Finset ι) (center p : ι → ℝ) : ℝ :=
  (Real.exp T / H) * (u / Real.exp U) * ∏ i ∈ S, giantCell (center i) (p i)

theorem counterpartArchimedean_nonneg (T U H u : ℝ) (S : Finset ι) (center p : ι → ℝ)
    (hH : 0 ≤ H) (hu : 0 ≤ u) : 0 ≤ counterpartArchimedean T U H u S center p :=
  mul_nonneg (mul_nonneg (div_nonneg (Real.exp_pos _).le hH) (div_nonneg hu (Real.exp_pos _).le))
    (Finset.prod_nonneg (fun _ _ => (giantCell_bounds _ _).1))

theorem counterpartArchimedean_le (T U H u WH Wu : ℝ) (S : Finset ι) (center p : ι → ℝ)
    (hH : 0 < H) (hu : 0 < u) (hlogH : T - WH ≤ Real.log H)
    (hlogu : Real.log u ≤ U + Wu) :
    counterpartArchimedean T U H u S center p ≤ Real.exp (WH + Wu) := by
  have h1 : Real.exp T / H ≤ Real.exp WH := by
    apply (Real.log_le_iff_le_exp (div_pos (Real.exp_pos _) hH)).mp
    rw [Real.log_div (Real.exp_pos _).ne' hH.ne',Real.log_exp]
    linarith
  have h2 : u / Real.exp U ≤ Real.exp Wu := by
    apply (Real.log_le_iff_le_exp (div_pos hu (Real.exp_pos _))).mp
    rw [Real.log_div hu.ne' (Real.exp_pos _).ne',Real.log_exp]
    linarith
  have hc : (∏ i ∈ S, giantCell (center i) (p i)) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => (giantCell_bounds _ _).1) (fun i _ => (giantCell_bounds _ _).2)
  calc
    _ ≤ (Real.exp WH * Real.exp Wu) * 1 :=
      mul_le_mul (mul_le_mul h1 h2 (div_pos hu (Real.exp_pos _)).le (Real.exp_pos _).le) hc
        (Finset.prod_nonneg (fun i _ => (giantCell_bounds _ _).1))
        (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
    _ = _ := by rw [mul_one,Real.exp_add]

theorem counterpartArchimedean_eq (T U H u : ℝ) (S : Finset ι) (center p : ι → ℝ)
    (hp : ∀ i ∈ S, 0 < p i) :
    counterpartArchimedean T U H u S center p =
      (Real.exp T / H) * (u / Real.exp U) *
        ∏ i ∈ S, smoothPartition (Real.log (p i) - center i) := by
  unfold counterpartArchimedean
  congr 1
  exact Finset.prod_congr rfl (fun i hi => giantCell_of_pos _ (hp i hi))

theorem counterpartArchimedean_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T U : ℝ) (H u : E → ℝ) (S : Finset ι) (center : ι → ℝ) (p : ι → E → ℝ) (x : E)
    (hH : ContDiffAt ℝ ∞ H x) (hu : ContDiffAt ℝ ∞ u x)
    (hp : ∀ i ∈ S, ContDiffAt ℝ ∞ (p i) x) (hH0 : H x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => counterpartArchimedean T U (H y) (u y) S center (fun i => p i y)) x := by
  exact ((contDiffAt_const.div hH hH0).mul (hu.div_const _)).mul
    (contDiffAt_prod (fun i hi => (giantCell_contDiff _).contDiffAt.comp x (hp i hi)))

end Ostmann.Arithmetic

end

end OAI
