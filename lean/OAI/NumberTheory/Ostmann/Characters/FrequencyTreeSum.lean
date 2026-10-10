import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.FrequencyTreeSum
universe u
variable {α:Type u}

@[reducible] def Assignment (S:List Bool→Finset α) : (k:ℕ)→List Bool→Type u
  | 0,p => {x:α // x∈S p}
  | k+1,p => {x:α // x∈S p} ×
      (Assignment S k (false::p) × Assignment S k (true::p))

@[reducible] instance assignmentFintype (S:List Bool→Finset α) (k:ℕ) (p:List Bool) :
    Fintype (Assignment S k p) := by
  induction k generalizing p with
  | zero => exact inferInstanceAs (Fintype {x:α // x∈S p})
  | succ k ih =>
    exact @instFintypeProd {x:α // x∈S p}
      (Assignment S k (false::p) × Assignment S k (true::p)) inferInstance
      (@instFintypeProd _ _ (ih _) (ih _))

def root (S:List Bool→Finset α) : {k:ℕ}→{p:List Bool}→Assignment S k p→α
  | 0,_,x => x.val
  | _+1,_,x => x.1.val

theorem root_mem (S:List Bool→Finset α) {k:ℕ} {p:List Bool}
    (x:Assignment S k p) : root S x∈S p := by
  cases k with
  | zero => exact x.property
  | succ k => exact x.1.property

def weight (S:List Bool→Finset α) (φ:List Bool→α→α→α→ℝ) :
    {k:ℕ}→{p:List Bool}→Assignment S k p→ℝ
  | 0,_,_ => 1
  | _+1,p,x => φ p x.1.val (root S x.2.1) (root S x.2.2) *
      weight S φ x.2.1 * weight S φ x.2.2

def total (S:List Bool→Finset α) (φ:List Bool→α→α→α→ℝ)
    (k:ℕ) (p:List Bool) : ℝ := ∑ x:Assignment S k p, weight S φ x

def budget (S:List Bool→Finset α) (C:List Bool→ℝ) : ℕ→List Bool→ℝ
  | 0,p => (S p).card
  | k+1,p => C p * budget S C k (false::p) * budget S C k (true::p)

private theorem weight_nonneg (S:List Bool→Finset α) (φ:List Bool→α→α→α→ℝ)
    (hφ:∀p s v w,0≤φ p s v w) {k:ℕ} {p:List Bool}
    (x:Assignment S k p) : 0≤weight S φ x := by
  induction k generalizing p with
  | zero => exact zero_le_one
  | succ k ih => exact mul_nonneg (mul_nonneg (hφ _ _ _ _) (ih _)) (ih _)

private theorem budget_nonneg (S:List Bool→Finset α) (C:List Bool→ℝ)
    (hC:∀p,0≤C p) (k:ℕ) (p:List Bool) : 0≤budget S C k p := by
  induction k generalizing p with
  | zero => exact Nat.cast_nonneg _
  | succ k ih => exact mul_nonneg (mul_nonneg (hC _) (ih _)) (ih _)

theorem total_succ (S:List Bool→Finset α) (φ:List Bool→α→α→α→ℝ)
    (k:ℕ) (p:List Bool) :
    total S φ (k+1) p =
      ∑ x:Assignment S k (false::p), ∑ y:Assignment S k (true::p),
        (∑ s∈S p,φ p s (root S x) (root S y))*weight S φ x*weight S φ y := by
  change (∑ z:({x:α // x∈S p} ×
      (Assignment S k (false::p) × Assignment S k (true::p))),
      φ p z.1.val (root S z.2.1) (root S z.2.2)*
        weight S φ z.2.1*weight S φ z.2.2) = _
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← Finset.sum_mul,← Finset.sum_mul]
  congr 2
  exact Finset.sum_coe_sort (S p) (fun s=>φ p s (root S x) (root S y))

theorem total_le_budget (S:List Bool→Finset α) (φ:List Bool→α→α→α→ℝ)
    (C:List Bool→ℝ) (hφ:∀p s v w,0≤φ p s v w) (hC:∀p,0≤C p)
    (hlocal:∀p v, v∈S (false::p)→∀w, w∈S (true::p)→
      (∑s∈S p,φ p s v w)≤C p) (k:ℕ) (p:List Bool) :
    total S φ k p≤budget S C k p := by
  induction k generalizing p with
  | zero =>
    change (∑ _x : ↥(S p), (1:ℝ)) ≤ ((S p).card:ℝ)
    simp
  | succ k ih =>
    rw [total_succ]
    calc
      _ ≤ ∑ x:Assignment S k (false::p), ∑ y:Assignment S k (true::p),
          C p*weight S φ x*weight S φ y := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro y hy
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (hlocal p _ (root_mem S x) _ (root_mem S y)) (weight_nonneg S φ hφ x))
          (weight_nonneg S φ hφ y)
      _ = C p*total S φ k (false::p)*total S φ k (true::p) := by
        simp only [total,← Finset.mul_sum,← Finset.sum_mul]
      _ ≤ C p*budget S C k (false::p)*budget S C k (true::p) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (ih _) (hC p)
        · exact ih _
        · exact Finset.sum_nonneg (fun x _=>weight_nonneg S φ hφ x)
        · exact mul_nonneg (hC p) (budget_nonneg S C hC k _)
      _ = budget S C (k+1) p := rfl

end Ostmann.Characters.FrequencyTreeSum

end

end OAI
