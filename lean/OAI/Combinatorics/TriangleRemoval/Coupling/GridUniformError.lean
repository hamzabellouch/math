import Mathlib
import OAI.Combinatorics.TriangleRemoval.Stability.GridCavityError

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
section GridRowBounds
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def gridUniformError (_H : τ → Finset ι) : ℝ :=
  ((Fintype.card τ : ℝ)^2 * Fintype.card ι) *
    Real.exp ((Fintype.card τ : ℝ) * Fintype.card ι)

omit [DecidableEq ι] [DecidableEq τ] in
lemma gridUniformError_nonneg (H : τ → Finset ι) : 0 ≤ gridUniformError H := by
  unfold gridUniformError
  positivity

lemma gridMessage_uniform_error (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) (e : ι) (p : Option τ) :
    |gridMessage H N N k e p - cavityLimit H e p ((k : ℝ)/N)| ≤
      gridUniformError H / N := by
  have h := (gridCavityError_coord H N k e p).trans (gridCavityError_bound H N k hk)
  simpa only [gridUniformError,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h

noncomputable def gridCandidateFailure (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (e : ι) (T : τ) : ℝ :=
  1 - (1/(N : ℝ)) * ∑ j ∈ Finset.range k,
    ∏ f ∈ (H T).erase e, gridMessage H N N j f (some T)

lemma gridCandidateFailure_error (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) (e : ι) (T : τ) :
    |gridCandidateFailure H N k e T -
        (1-messageIntegral H (cavityLimit H) e T ((k : ℝ)/N))| ≤
      ((Fintype.card ι : ℝ)*gridUniformError H +
        (Fintype.card ι : ℝ)*Fintype.card τ)/N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hE : 0 ≤ gridUniformError H / N := div_nonneg (gridUniformError_nonneg H) hN.le
  have hs : (∑ j ∈ Finset.range k, gridCavityError H N j) ≤ gridUniformError H := by
    calc
      _ ≤ ∑ _j ∈ Finset.range k, gridUniformError H / N := by
        apply Finset.sum_le_sum
        intro j hj
        have hh := gridCavityError_bound H N j ((Finset.mem_range.mp hj).le.trans hk)
        simpa only [gridUniformError,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
      _ = (k : ℝ) * (gridUniformError H / N) := by simp
      _ ≤ (N : ℝ) * (gridUniformError H / N) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hE
      _ = gridUniformError H := by field_simp
  unfold gridCandidateFailure
  rw [sub_sub_sub_cancel_left,abs_sub_comm]
  calc
    _ ≤ ((Fintype.card ι : ℝ)/N) * ∑ j ∈ Finset.range k, gridCavityError H N j +
        ((Fintype.card ι : ℝ)*Fintype.card τ)/N :=
      grid_message_integral_error H N k hk e T
    _ ≤ ((Fintype.card ι : ℝ)/N)*gridUniformError H +
        ((Fintype.card ι : ℝ)*Fintype.card τ)/N := by gcongr
    _ = _ := by ring

lemma gridAnswer_uniform_error (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) (focus : Finset ι) (p : Option τ) :
    |gridAnswerProbability H N N k focus p -
        ∏ e ∈ focus, cavityLimit H e p ((k : ℝ)/N)| ≤
      (focus.card : ℝ)*gridUniformError H/N := by
  rw [gridAnswerProbability_factor]
  calc
    _ ≤ ∑ e ∈ focus, |gridMessage H N N k e p - cavityLimit H e p ((k : ℝ)/N)| :=
      abs_prod_sub_prod_le_sum _ _ _ (fun e _ => gridMessage_mem_unit H N N k e p)
        (fun e _ => cavityLimit_mem_unit H e p _)
    _ ≤ ∑ _e ∈ focus, gridUniformError H/N :=
      Finset.sum_le_sum (fun e _ => gridMessage_uniform_error H N k hk e p)
    _ = _ := by simp; ring

omit [Fintype ι] in
lemma gridCandidateFailure_product (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) (focus : Finset ι) (p : Option τ) :
    (∏ a : gridCandidates H focus p, gridCandidateFailure H N k a.val.1 a.val.2) =
      gridAnswerProbability H N N k focus p := by
  change (∏ a : gridCandidates H focus p,
    (fun a : ι × τ => gridCandidateFailure H N k a.1 a.2) a.val) = _
  rw [Finset.prod_coe_sort (gridCandidates H focus p)
    (fun a : ι × τ => gridCandidateFailure H N k a.1 a.2),
    prod_gridCandidates,gridAnswerProbability_factor]
  apply Finset.prod_congr rfl
  intro e _
  exact (gridMessage_exact_range H N k hk e p).symm

end GridRowBounds
end SharpTerminalLeave

end

end OAI
