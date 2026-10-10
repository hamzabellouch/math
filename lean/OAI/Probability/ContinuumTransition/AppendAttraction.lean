import OAI.Probability.ContinuumTransition.MaskedComparison

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

def prepend (a : ℝ) (σ : ℕ → ℝ) : ℕ → ℝ
  | 0 => a
  | n+1 => σ n

@[simp] theorem prepend_zero (a : ℝ) (σ : ℕ → ℝ) : prepend a σ 0 = a := rfl
@[simp] theorem prepend_succ (a : ℝ) (σ : ℕ → ℝ) (n : ℕ) : prepend a σ (n+1) = σ n := rfl

theorem summable_prepend (a : ℝ) {σ : ℕ → ℝ} (hs : Summable σ) : Summable (prepend a σ) := by
  exact (summable_nat_add_iff 1).mp hs

theorem tsum_prepend (a : ℝ) {σ : ℕ → ℝ} (hs : Summable σ) :
    ∑' n, prepend a σ n = a+∑' n, σ n := by
  exact (summable_prepend a hs).tsum_eq_zero_add

theorem prepend_nonneg {a : ℝ} {σ : ℕ → ℝ} (ha : 0 ≤ a) (hσ : ∀ n, 0 ≤ σ n) :
    ∀ n, 0 ≤ prepend a σ n
  | 0 => ha
  | n+1 => hσ n

theorem prepend_ge_one {a : ℝ} {σ : ℕ → ℝ} (ha : 1 ≤ a) (hσ : ∀ n, 1 ≤ σ n) :
    ∀ n, 1 ≤ prepend a σ n
  | 0 => ha
  | n+1 => hσ n

theorem attraction_prepend (t : ℝ) {a S : ℝ} {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (r : ℝ) :
    attraction t (prepend a σ) (prepend S R) r = t*a*scaledKernelProfile S r+attraction t σ R r := by
  unfold attraction
  have he : (fun n => prepend a σ n*scaledKernelProfile (prepend S R n) r) =
      prepend (a*scaledKernelProfile S r) (fun n => σ n*scaledKernelProfile (R n) r) := by
    funext n; cases n <;> rfl
  rw [he, tsum_prepend _ (summable_attraction_terms hσ hR hs r)]
  ring

theorem physicalProfile_prepend (t : ℝ) {a S : ℝ} {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (r : ℝ) :
    physicalProfile t (prepend a σ) (prepend S R) r = physicalProfile t σ R r-t*a*scaledKernelProfile S r := by
  unfold physicalProfile
  rw [attraction_prepend t hσ hR hs]
  ring

theorem attraction_zero (t : ℝ) (R : ℕ → ℝ) (r : ℝ) : attraction t (fun _ => 0) R r = 0 := by
  simp [attraction]

theorem cutReference_prepend (t a S : ℝ) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (q : ℕ) (x y : Space) :
    cutReference t (prepend 0 σ) (prepend a (fun _ => 0)) (prepend S R) q x y =
      blockCut q (fun x y => physicalProfile t σ R ‖x-y‖) x y-t*a*scaledKernelProfile S ‖x-y‖ := by
  unfold cutReference
  simp only [physicalProfile_prepend t hσ hR hs, mul_zero, zero_mul, sub_zero]
  rw [attraction_prepend t (fun _ => le_refl 0) hR (summable_zero), attraction_zero, add_zero]

end ContinuumTemperature
end

end OAI
