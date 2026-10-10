import OAI.Probability.InvariantIsing.Cavity.ConsecutiveFieldPressure

namespace OAI

/-! Repeating a finite field block multiplies each group size by the
number of repetitions and preserves its attainable magnetizations. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

def consecutiveSiteGroup {n : ℕ} {A : Type*} (K : ℕ) (group : Fin n → A) : Fin (K*n) → A :=
  fun i => group (finProdFinEquiv.symm i).2

lemma consecutiveSiteGroup_size {n K : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin n → A) (a : A) :
    spinGroupSize (consecutiveSiteGroup K group) a=K*spinGroupSize group a := by
  simp only [spinGroupSize, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin K × Fin n ≃ Fin (K*n))]
  simp only [consecutiveSiteGroup, Equiv.symm_apply_apply, Fintype.sum_prod_type]
  change (∑ _ : Fin K, (∑ i : Fin n, if group i=a then 1 else 0)) = _
  simp

lemma consecutiveSiteGroup_attainable {n K : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin n → A) (k : A → ℕ) (hk : ∀ a, k a ≤ spinGroupSize group a) :
    ∀ a, K*k a ≤ spinGroupSize (consecutiveSiteGroup K group) a := by
  intro a
  rw [consecutiveSiteGroup_size]
  exact Nat.mul_le_mul_left K (hk a)

lemma consecutiveSiteGroup_proportion {n K : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin n → A) (γ : A → ℝ)
    (hcount : ∀ a, (spinGroupSize group a : ℝ)=n*γ a) :
    ∀ a, (spinGroupSize (consecutiveSiteGroup K group) a : ℝ)=(K*n : ℕ)*γ a := by
  intro a
  rw [consecutiveSiteGroup_size, Nat.cast_mul, hcount, Nat.cast_mul]
  ring

lemma consecutiveSiteGroup_magnetization {n K : ℕ} {A : Type*} [DecidableEq A]
    (group : Fin n → A) (k : A → ℕ) (mag : A → ℝ)
    (hk : ∀ a, (k a : ℝ)=spinGroupSize group a*((1+mag a)/2)) :
    ∀ a, (K*k a : ℕ)= (spinGroupSize (consecutiveSiteGroup K group) a : ℝ)*((1+mag a)/2) := by
  intro a
  rw [consecutiveSiteGroup_size, Nat.cast_mul, hk, Nat.cast_mul]
  ring

end InvariantIsing

end

end OAI
