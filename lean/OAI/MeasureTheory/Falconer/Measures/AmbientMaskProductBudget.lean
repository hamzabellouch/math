import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace OAI

/-! # Polynomial mixed-derivative cost of an actual finite mask product

The zeroth-order bound is one. Consequently no constant is raised to the
number of descriptors: order `k` costs only `card^k`.
-/

namespace Falconer
open scoped ContDiff

variable {E A ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedCommRing A] [NormedAlgebra ℝ A] [NormOneClass A] [DecidableEq ι]

theorem ambient_mask_product_derivatives (S : Finset ι) (f : ι → E → A)
    {D : ℝ} (hD : 0 ≤ D) (K : ℕ) (x : E)
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ S, ∀ k ≤ K, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ D^k) :
    ∀ k ≤ K, ‖iteratedFDeriv ℝ k (fun z => ∏ i ∈ S, f i z) x‖ ≤ ((S.card : ℝ)*D)^k := by
  induction S using Finset.induction_on with
  | empty =>
    intro k _
    cases k with
    | zero => simp
    | succ k => simp [iteratedFDeriv_succ_const]
  | @insert a S ha ih =>
    have hfs : ∀ i ∈ S, ContDiff ℝ ∞ (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hbs : ∀ i ∈ S, ∀ k ≤ K, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ D^k :=
      fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hih := ih hfs hbs
    intro k hk
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hfp : ContDiff ℝ ∞ (fun z => ∏ i ∈ S, f i z) := contDiff_prod hfs
    simp only [Finset.prod_insert ha,Finset.card_insert_of_notMem ha,Nat.cast_add,Nat.cast_one]
    apply (norm_iteratedFDeriv_mul_le hfa hfp x (by simp : (k : ℕ∞ω) ≤ ∞)).trans
    calc
      _ ≤ ∑ l ∈ Finset.range (k+1), (k.choose l : ℝ)*D^l*((S.card : ℝ)*D)^(k-l) := by
        apply Finset.sum_le_sum
        intro l hl
        have hlk : l ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hb a (Finset.mem_insert_self _ _) l (hlk.trans hk))
            (Nat.cast_nonneg _))
          (hih (k-l) ((Nat.sub_le _ _).trans hk)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hD _))
      _ = (D+(S.card : ℝ)*D)^k := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by congr 1; ring

/-- A fixed positive-order derivative constant is absorbed into each
differentiated mask's scale, never into every undifferentiated mask. -/
theorem ambient_mask_product_budget (S : Finset ι) (f : ι → E → A)
    {C D : ℝ} (hC : 1 ≤ C) (hD : 0 ≤ D) (K : ℕ) (x : E)
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i)) (hzero : ∀ i ∈ S, ‖f i x‖ ≤ 1)
    (hb : ∀ i ∈ S, ∀ k, 1 ≤ k → k ≤ K → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ C*D^k) :
    ∀ k ≤ K, ‖iteratedFDeriv ℝ k (fun z => ∏ i ∈ S, f i z) x‖ ≤ ((S.card : ℝ)*C*D)^k := by
  have hscaled : ∀ i ∈ S, ∀ k ≤ K, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ (C*D)^k := by
    intro i hi k hk
    cases k with
    | zero => simpa only [norm_iteratedFDeriv_zero,pow_zero] using hzero i hi
    | succ k =>
      apply (hb i hi (k+1) (by omega) hk).trans
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ hC (by omega)) (pow_nonneg hD _)
  simpa only [mul_assoc] using ambient_mask_product_derivatives S f
    (mul_nonneg (zero_le_one.trans hC) hD) K x hf hscaled

end Falconer

end OAI
