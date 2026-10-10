import OAI.Analysis.FreeEntropy.CumulantSeries

namespace OAI

universe u1 u2 u3

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type u1} [Fintype α]

abbrev DegreeSpace (α : Type u2) [Fintype α] (n : ℕ) := EuclideanSpace ℂ (List.Vector α n)
def degreeVector (f : Series α) (n : ℕ) : DegreeSpace α n := WithLp.toLp 2 (fun w => f w.val)
def degreeNorm (f : Series α) (n : ℕ) : ℝ := ‖degreeVector f n‖

@[simp] theorem degreeVector_apply (f : Series α) (n : ℕ) (w : List.Vector α n) :
    degreeVector f n w = f w.val := rfl
@[simp] theorem degreeNorm_nonneg (f : Series α) (n : ℕ) : 0 ≤ degreeNorm f n := norm_nonneg _
 theorem degreeNorm_sq (f : Series α) (n : ℕ) :
    degreeNorm f n ^ 2 = ∑ w : List.Vector α n, ‖f w.val‖ ^ 2 := by
  exact EuclideanSpace.norm_sq_eq _
 theorem degreeVector_add (f g : Series α) (n : ℕ) :
    degreeVector (f+g) n = degreeVector f n + degreeVector g n := rfl
 theorem degreeVector_smul (c : ℂ) (f : Series α) (n : ℕ) :
    degreeVector (c • f) n = c • degreeVector f n := rfl
 theorem degreeNorm_add_le (f g : Series α) (n : ℕ) :
    degreeNorm (f+g) n ≤ degreeNorm f n + degreeNorm g n := by
  unfold degreeNorm
  rw [degreeVector_add]
  exact norm_add_le _ _
@[simp] theorem degreeNorm_smul (c : ℂ) (f : Series α) (n : ℕ) :
    degreeNorm (c • f) n = ‖c‖ * degreeNorm f n := by
  unfold degreeNorm
  rw [degreeVector_smul]
  exact norm_smul _ _
@[simp] theorem degreeNorm_zero (n : ℕ) : degreeNorm (0 : Series α) n = 0 := norm_zero
 theorem degreeNorm_congr {f g : Series α} (n : ℕ)
    (h : ∀ w, w.length = n → f w = g w) : degreeNorm f n = degreeNorm g n := by
  apply congrArg norm
  ext w : 1
  exact h w.val w.prop
 theorem degreeNorm_le_of_coeff {f g : Series α} {n : ℕ}
    (h : ∀ w, w.length = n → ‖f w‖ ≤ ‖g w‖) : degreeNorm f n ≤ degreeNorm g n := by
  apply (sq_le_sq₀ (degreeNorm_nonneg _ _) (degreeNorm_nonneg _ _)).mp
  rw [degreeNorm_sq, degreeNorm_sq]
  exact sum_le_sum fun w _ => pow_le_pow_left₀ (norm_nonneg _) (h w.val w.prop) 2
 theorem degreeNorm_sum_le {ι : Type u3} (s : Finset ι) (f : ι → Series α) (n : ℕ) :
    degreeNorm (∑ i ∈ s, f i) n ≤ ∑ i ∈ s, degreeNorm (f i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    exact (degreeNorm_add_le _ _ _).trans (add_le_add_right ih _)

 def vectorSplit (m n : ℕ) : List.Vector α (m+n) ≃ List.Vector α m × List.Vector α n where
  toFun w := (⟨w.val.take m, by simp [w.prop]⟩, ⟨w.val.drop m, by simp [w.prop]⟩)
  invFun v := ⟨v.1.val ++ v.2.val, by simp [v.1.prop, v.2.prop]⟩
  left_inv w := by apply Subtype.ext; exact List.take_append_drop _ _
  right_inv v := by
    apply Prod.ext <;> apply Subtype.ext
    · exact List.take_left' v.1.prop
    · exact List.drop_left' v.1.prop

 theorem degreeNorm_tensor (f g : Series α) (m n : ℕ) :
    degreeNorm (fun w => f (w.take m) * g (w.drop m)) (m+n) =
      degreeNorm f m * degreeNorm g n := by
  apply (sq_eq_sq₀ (degreeNorm_nonneg _ _) (mul_nonneg (degreeNorm_nonneg _ _) (degreeNorm_nonneg _ _))).mp
  rw [mul_pow, degreeNorm_sq, degreeNorm_sq, degreeNorm_sq]
  have h := (vectorSplit (α := α) m n).sum_comp
    (fun v : List.Vector α m × List.Vector α n => ‖f v.1.val‖ ^ 2 * ‖g v.2.val‖ ^ 2)
  calc
    _ = ∑ v : List.Vector α (m+n), ‖f (v.val.take m)‖^2 * ‖g (v.val.drop m)‖^2 := by
      simp only [norm_mul, mul_pow]
    _ = ∑ v : List.Vector α m × List.Vector α n, ‖f v.1.val‖^2 * ‖g v.2.val‖^2 := h
    _ = _ := by rw [Fintype.sum_prod_type, sum_mul_sum]

 theorem degreeNorm_conv_le (f g : Series α) (n : ℕ) :
    degreeNorm (conv f g) n ≤ ∑ k ∈ range (n+1), degreeNorm f k * degreeNorm g (n-k) := by
  have h : degreeNorm (conv f g) n =
      degreeNorm (∑ k ∈ range (n+1), fun w => f (w.take k) * g (w.drop k)) n := by
    apply degreeNorm_congr
    intro w hw
    simp only [conv_sum_splits, hw, Finset.sum_apply]
  rw [h]
  apply (degreeNorm_sum_le _ _ _).trans
  apply sum_le_sum
  intro k hk
  have hn : k + (n-k) = n := Nat.add_sub_of_le (Nat.le_of_lt_succ (mem_range.mp hk))
  simpa only [hn] using le_of_eq (degreeNorm_tensor f g k (n-k))

end FiniteEntropySeparation.FreeSeries

end

end OAI
