import Mathlib
import OAI.Computability.MaxCut.Estimates.Dictator

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset OptimalMaxCut.Unweighted

namespace Law
variable {I : Type} [Fintype I]

/-- Downward rounding is performed BEFORE aggregation. Thus every output mass
has the same polynomially sized integer denominator; no product of all input
vertex degrees has to be represented as a unary integer. -/
noncomputable def gridWeight (P : ℕ) (a : ℚ) : ℚ := (⌊(P : ℚ) * a⌋₊ : ℚ) / P

 theorem gridWeight_nonneg (P : ℕ) (a : ℚ) : 0 ≤ gridWeight P a := by
  unfold gridWeight; positivity

 theorem gridWeight_le (P : ℕ) (hP : 0 < P) (a : ℚ) (ha : 0 ≤ a) :
    gridWeight P a ≤ a := by
  have hPr : (0 : ℚ) < P := by exact_mod_cast hP
  rw [gridWeight, div_le_iff₀ hPr]
  simpa [mul_comm] using Nat.floor_le (mul_nonneg hPr.le ha)

 theorem gridWeight_error (P : ℕ) (hP : 0 < P) (a : ℚ) :
    a - gridWeight P a ≤ 1 / (P : ℚ) := by
  have hPr : (0 : ℚ) < P := by exact_mod_cast hP
  have h := Nat.lt_floor_add_one ((P : ℚ) * a)
  unfold gridWeight
  apply (le_div_iff₀ hPr).mpr
  rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hPr)]
  nlinarith

noncomputable def grid (p : Law I) (P : ℕ) (hP : 0 < P) : Law (Option I) where
  weight
    | none => 1 - ∑ i, gridWeight P (p.weight i)
    | some i => gridWeight P (p.weight i)
  nonneg
    | none => by
        have h := sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) =>
          gridWeight_le P hP (p.weight i) (p.nonneg i))
        rw [p.total] at h
        linarith
    | some i => gridWeight_nonneg _ _
  total := by simp [Fintype.sum_option]

 theorem grid_average (p : Law I) (P : ℕ) (hP : 0 < P) (f : Option I → ℝ)
    (hzero : f none = 0) :
    (p.grid P hP).avg f = ∑ i, (gridWeight P (p.weight i) : ℝ) * f (some i) := by
  simp only [avg, Fintype.sum_option, grid, hzero, mul_zero, zero_add]

 theorem grid_average_bounds (p : Law I) (P : ℕ) (hP : 0 < P) (f : I → ℝ)
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) :
    let rounded := ∑ i, (gridWeight P (p.weight i) : ℝ) * f i
    rounded ≤ p.avg f ∧ p.avg f - rounded ≤ Fintype.card I / (P : ℝ) := by
  dsimp only
  have hw (i : I) : (gridWeight P (p.weight i) : ℝ) ≤ (p.weight i : ℝ) := by
    exact_mod_cast gridWeight_le P hP _ (p.nonneg i)
  have he (i : I) : (p.weight i : ℝ) - (gridWeight P (p.weight i) : ℝ) ≤ 1 / (P : ℝ) := by
    have hh : ((p.weight i - gridWeight P (p.weight i) : ℚ) : ℝ) ≤
        ((1 / (P : ℚ) : ℚ) : ℝ) := by exact_mod_cast gridWeight_error P hP (p.weight i)
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using hh
  constructor
  · exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hw i) (hf0 i))
  · rw [avg, ← sum_sub_distrib]
    calc
      _ ≤ ∑ _ : I, 1 / (P : ℝ) := sum_le_sum (fun i _ => by
        have h := mul_le_of_le_one_right (sub_nonneg.mpr (hw i)) (hf1 i)
        nlinarith [he i])
      _ = _ := by simp [div_eq_mul_inv]

end Law

/-- Lost mass becomes a loop, which is deleted by exactly the original
aggregation. It is never renormalized into non-loop edges. -/
noncomputable def roundedWeights {I : Type} [Fintype I] {N : ℕ}
    (p : Law I) (endpoints : I → Fin N × Fin N) (v0 : Fin N)
    (P : ℕ) (hP : 0 < P) : Fin N → Fin N → ℚ :=
  aggregate ((p.grid P hP).push (fun
    | none => (v0,v0)
    | some i => endpoints i))

 theorem roundedWeights_cut_error {I : Type} [Fintype I] {N : ℕ}
    (p : Law I) (query : I → Fin N × Fin N) (v0 : Fin N)
    (P : ℕ) (hP : 0 < P) (σ : Fin N → Bool) :
    let w := aggregate (p.push query)
    let w' := roundedWeights p query v0 P hP
    weightedCut (fun u v => (w' u v : ℝ)) σ ≤ weightedCut (fun u v => (w u v : ℝ)) σ ∧
      weightedCut (fun u v => (w u v : ℝ)) σ -
        weightedCut (fun u v => (w' u v : ℝ)) σ ≤ Fintype.card I / (P : ℝ) := by
  dsimp only
  rw [aggregate_cut, Law.push_average, roundedWeights, aggregate_cut, Law.push_average,
    Law.grid_average _ _ _ _ (by simp)]
  exact Law.grid_average_bounds p P hP (fun i => if σ (query i).1 ≠ σ (query i).2 then 1 else 0)
    (fun i => by split_ifs <;> norm_num) (fun i => by split_ifs <;> norm_num)

 theorem roundedWeights_max_error {I : Type} [Fintype I] {N : ℕ}
    (p : Law I) (query : I → Fin N × Fin N) (v0 : Fin N)
    (P : ℕ) (hP : 0 < P) :
    let w := aggregate (p.push query)
    let w' := roundedWeights p query v0 P hP
    weightedMax (fun u v => (w' u v : ℝ)) ≤ weightedMax (fun u v => (w u v : ℝ)) ∧
      weightedMax (fun u v => (w u v : ℝ)) -
        weightedMax (fun u v => (w' u v : ℝ)) ≤ Fintype.card I / (P : ℝ) := by
  dsimp only
  obtain ⟨σ, hσ⟩ := weightedMax_attained (fun u v =>
    (roundedWeights p query v0 P hP u v : ℝ))
  obtain ⟨τ, hτ⟩ := weightedMax_attained (fun u v => (aggregate (p.push query) u v : ℝ))
  constructor
  · have h := (roundedWeights_cut_error p query v0 P hP σ).1
    exact hσ.symm.trans_le (h.trans (weightedCut_le_max _ _))
  · have h := (roundedWeights_cut_error p query v0 P hP τ).2
    have h' := weightedCut_le_max (fun u v => (roundedWeights p query v0 P hP u v : ℝ)) τ
    rw [hτ] at h
    linarith

end OptimalMaxCut.LongCode

end

end OAI
