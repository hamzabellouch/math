import OAI.Analysis.TriangularHilbert.IntegratedDissipation

namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma telescope_with_jumps (E : ℕ → ℕ → ℝ) (n : ℕ) (hn : 0 ≤ E n n) :
    (∑ k ∈ Finset.range n, (E k k-E k (k+1))) ≤ E 0 0+
      ∑ k ∈ Finset.range n, |E (k+1) (k+1)-E k (k+1)| := by
  have he : (∑ k ∈ Finset.range n, (E k k-E k (k+1))) = E 0 0-E n n+
      ∑ k ∈ Finset.range n, (E (k+1) (k+1)-E k (k+1)) := by
    clear hn
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ,Finset.sum_range_succ,ih]; ring
  rw [he]
  have hi := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) =>
    le_abs_self (E (k+1) (k+1)-E k (k+1)))
  linarith

def opening (a s : ℝ) (A : ℂ) : ℂ := if a ≤ s then A else 0

def windowMask (a b s : ℝ) (A : ℂ) : ℂ := if a ≤ s ∧ s < b then A else 0

lemma windowMask_eq_sub (a b s : ℝ) (hab : a ≤ b) (A : ℂ) :
    windowMask a b s A = opening a s A-opening b s A := by
  unfold windowMask opening
  split_ifs <;> simp_all <;> linarith

lemma windowMask_norm_le (a b s : ℝ) (A : ℂ) : ‖windowMask a b s A‖ ≤ ‖A‖ := by
  unfold windowMask
  split_ifs <;> simp

lemma sum_opening_variation (t : ℕ → ℝ) (ht : Monotone t) (a : ℝ) (A : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range n, ‖opening a (t (k+1)) A-opening a (t k) A‖) =
      (if a ≤ t n then ‖A‖ else 0)-(if a ≤ t 0 then ‖A‖ else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    have hh := ht (Nat.le_succ n)
    have h0 := ht (Nat.zero_le n)
    unfold opening
    split_ifs <;> simp_all <;> linarith

lemma sum_windowMask_variation (t : ℕ → ℝ) (ht : Monotone t) (a b : ℝ) (hab : a ≤ b)
    (A : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range n, ‖windowMask a b (t (k+1)) A-windowMask a b (t k) A‖) ≤ 2*‖A‖ := by
  have hi := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) =>
    norm_sub_le (opening a (t (k+1)) A-opening a (t k) A)
      (opening b (t (k+1)) A-opening b (t k) A))
  have he (k : ℕ) : windowMask a b (t (k+1)) A-windowMask a b (t k) A =
      (opening a (t (k+1)) A-opening a (t k) A)-(opening b (t (k+1)) A-opening b (t k) A) := by
    rw [windowMask_eq_sub _ _ _ hab,windowMask_eq_sub _ _ _ hab]
    ring
  simp_rw [he]
  apply hi.trans
  rw [Finset.sum_add_distrib,sum_opening_variation t ht a A n,sum_opening_variation t ht b A n]
  split_ifs <;> linarith [norm_nonneg A]
end
end TriangularHilbert
end

end OAI
