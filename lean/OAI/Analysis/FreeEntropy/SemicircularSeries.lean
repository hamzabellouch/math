import OAI.Analysis.FreeEntropy.SeriesAnalytic

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [DecidableEq α]

def letter (i : α) : Series α
  | [j] => if j=i then 1 else 0
  | _ => 0
def quadratic : Series α
  | [i,j] => if j=i then 1 else 0
  | _ => 0
@[simp] theorem letter_nil (i : α) : letter i [] = 0 := rfl
@[simp] theorem quadratic_nil : (quadratic : Series α) [] = 0 := rfl
 theorem deriv_letter (i j : α) : deriv j (letter i) = if j=i then unit else 0 := by
  funext w
  cases w with
  | nil => by_cases h : j=i <;> simp [deriv, letter, unit, h]
  | cons a w => cases w <;> by_cases h : j=i <;> simp [deriv, letter, unit, h]
 theorem subst_letter_cons (M : Series α) (i j : α) (w : List α) :
    subst M (letter i) (j::w) = if j=i then M w else 0 := by
  rw [subst_cons, deriv_letter]
  split_ifs <;> simp
 theorem deriv_quadratic (i : α) : deriv i (quadratic : Series α) = letter i := by
  funext w
  cases w with
  | nil => rfl
  | cons a w => cases w <;> rfl

 theorem quadratic_subst_derivative {n : ℕ} (M : Series (Fin n)) (i : Fin n) (w : List (Fin n)) :
    subst M quadratic (i::w) = ∑ r : Fin w.length, if w[r.val] = i then
      M (w.take r.val) * M (w.drop (r.val+1)) else 0 := by
  rw [subst_cons, deriv_quadratic, conv_sum_splits, sum_range_succ]
  simp only [List.take_length, List.drop_length, subst_nil, letter_nil, mul_zero, add_zero]
  rw [← Fin.sum_univ_eq_sum_range (fun k => M (w.take k) * subst M (letter i) (w.drop k))]
  apply sum_congr rfl
  intro k hk
  rw [List.drop_eq_getElem_cons k.isLt, subst_letter_cons]
  split_ifs <;> simp

def fockMoments (p : ℕ) : Series (Fin p) := wordMoment (Fock.tracialVector (Fin p)) Fock.semicircular
 theorem fockMoments_eq (p : ℕ) : fockMoments p = unit + subst (fockMoments p) quadratic := by
  funext w
  cases w with
  | nil => simp [fockMoments]
  | cons i w =>
    simp only [Pi.add_apply, unit_cons, zero_add, quadratic_subst_derivative]
    exact Fock.semicircular_integration_by_parts i w
 theorem fockMoments_moments (p : ℕ) : fockMoments p = moments quadratic :=
    moments_unique quadratic_nil (fockMoments_eq p)

variable [Fintype α]
 theorem degreeNorm_succ_sq {α : Type} [DecidableEq α] [Fintype α] (f : Series α) (n : ℕ) :
    degreeNorm f (n+1)^2 = ∑ a : α, degreeNorm (deriv a f) n ^ 2 := by
  rw [degreeNorm_sq]
  have he := (vectorCons (α := α) n).sum_comp
    (fun w : List.Vector α (n+1) => ‖f w.val‖^2)
  rw [← he, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a ha
  exact (degreeNorm_sq (deriv a f) n).symm
 theorem degreeNorm_letter_one (i : α) : degreeNorm (letter i) 1 = 1 := by
  apply (sq_eq_sq₀ (degreeNorm_nonneg _ _) (by norm_num : (0:ℝ) ≤ 1)).mp
  rw [degreeNorm_succ_sq]
  simp only [deriv_letter, degreeNorm_nil, ite_apply, unit_nil, Pi.zero_apply]
  calc
    _ = ∑ a : α, if a=i then (1:ℝ) else 0 := by
      apply sum_congr rfl
      intro a ha
      split_ifs <;> norm_num
    _ = _ := by simp
 theorem degreeNorm_quadratic_sq : degreeNorm (quadratic : Series α) 2 ^ 2 = Fintype.card α := by
  rw [degreeNorm_succ_sq]
  simp [deriv_quadratic, degreeNorm_letter_one]
 theorem degreeNorm_quadratic_other {n : ℕ} (hn : n ≠ 2) :
    degreeNorm (quadratic : Series α) n = 0 := by
  apply (degreeNorm_congr (g := 0) n ?_).trans (degreeNorm_zero n)
  intro w hw
  cases w with
  | nil => rfl
  | cons a w =>
    cases w with
    | nil => rfl
    | cons b w =>
      cases w with
      | nil => simp at hw; omega
      | cons c w => rfl
 theorem degreeNorm_quadratic : degreeNorm (quadratic : Series α) 2 = Real.sqrt (Fintype.card α) := by
  apply (sq_eq_sq₀ (degreeNorm_nonneg _ _) (Real.sqrt_nonneg _)).mp
  rw [degreeNorm_quadratic_sq, Real.sq_sqrt (by positivity)]
 theorem quadratic_weight_le {r : ℝ} (_hr : 0 ≤ r) (N : ℕ) :
    seriesWeight (quadratic : Series α) r N ≤ r^2 * Real.sqrt (Fintype.card α) := by
  unfold seriesWeight truncEval
  calc
    _ = ∑ k ∈ range (N+1), if k=2 then r^2 * Real.sqrt (Fintype.card α) else 0 := by
      apply sum_congr rfl
      intro k hk
      by_cases h : k = 2
      · subst k; simp [degreeNorm_quadratic]
      · simp [h, degreeNorm_quadratic_other h]
    _ ≤ _ := by simp only [sum_ite_eq']; split_ifs <;> first | exact le_rfl | positivity

 theorem fockMoments_norm_le {p : ℕ} (hp : 0 < p) (n : ℕ) :
    degreeNorm (fockMoments p) n ≤ (2 * Real.sqrt (Real.sqrt p))^n := by
  let q := Real.sqrt (Real.sqrt p)
  have hq : 0 < q := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hp))
  have hq2 : q^2 = Real.sqrt p := Real.sq_sqrt (Real.sqrt_nonneg _)
  let r := (2*q)⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  have hw (N : ℕ) : seriesWeight (quadratic : Series (Fin p)) (2*r) N ≤ 1 := by
    apply (quadratic_weight_le (by positivity) N).trans
    simp only [Fintype.card_fin]
    rw [← hq2]
    dsimp [r]
    field_simp
    norm_num
  have hm (N : ℕ) : seriesWeight (moments (quadratic : Series (Fin p))-unit) r N ≤ 1 :=
    moments_tail_weight quadratic_nil hr.le (by norm_num) le_rfl hw N
  cases n with
  | zero => simp [fockMoments]
  | succ n =>
    rw [fockMoments_moments]
    have hh := degreeNorm_le_of_weight hr hm (n+1)
    rw [degreeNorm_sub_unit_pos _ (by omega)] at hh
    simpa [r, q] using hh

end FiniteEntropySeparation.FreeSeries

end

end OAI
