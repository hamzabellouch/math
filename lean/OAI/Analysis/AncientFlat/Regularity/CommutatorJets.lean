import Mathlib

namespace OAI
noncomputable section
open scoped ContDiff
namespace ParabolicCommutator
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
def commutator (f : V → ℝ) (g : V → E) (x : V) :=
  iteratedFDeriv ℝ 4 (fun y => f y • g y) x-f x • iteratedFDeriv ℝ 4 g x
lemma commutator_eq (f : V → ℝ) (g : V → E) (x : V)
    (hf : ContDiff ℝ 4 f) (hg : ContDiff ℝ 4 g) :
    commutator f g x = iteratedFDeriv ℝ 4 (fun y => (f y-f x) • g y) x := by
  have he : (fun y => (f y-f x) • g y) = (fun y => f y • g y)-(fun y => f x • g y) := by
    funext y; exact sub_smul _ _ _
  rw [he,iteratedFDeriv_sub (f := fun y => f y • g y) (g := fun y => f x • g y) (hf.smul hg) (hg.const_smul (f x)),Pi.sub_apply,
    iteratedFDeriv_const_smul_apply' hg.contDiffAt]
  rfl
lemma jet_sub_value {n : ℕ} (hn : n≠0) (f : V → ℝ) (x : V)
    (hf : ContDiff ℝ n f) :
    iteratedFDeriv ℝ n (fun y => f y-f x) x=iteratedFDeriv ℝ n f x := by
  change iteratedFDeriv ℝ n (f-(fun _ => f x)) x=_
  rw [iteratedFDeriv_sub hf contDiff_const,Pi.sub_apply,iteratedFDeriv_const_of_ne hn]
  simp

lemma norm_commutator_le (f : V → ℝ) (g : V → E) (x : V)
    (hf : ContDiff ℝ 4 f) (hg : ContDiff ℝ 4 g) (A B : ℝ) (hA : 0≤A) (_ : 0≤B)
    (hfj : ∀ n : ℕ, 1≤n → n≤4 → ‖iteratedFDeriv ℝ n f x‖≤A)
    (hgj : ∀ n : ℕ, n≤3 → ‖iteratedFDeriv ℝ n g x‖≤B) :
    ‖commutator f g x‖≤15*A*B := by
  rw [commutator_eq f g x hf hg]
  have hb := norm_iteratedFDeriv_smul_le (f := fun y => f y-f x) (hf.sub contDiff_const) hg x
    (by norm_num : (4:ℕ)≤(4:WithTop ℕ∞))
  have hs : ∀ n : ℕ, n∈Finset.range 5 →
      ((4:ℕ).choose n : ℝ)*‖iteratedFDeriv ℝ n (fun y => f y-f x) x‖*
        ‖iteratedFDeriv ℝ (4-n) g x‖ ≤
      if n=0 then 0 else ((4:ℕ).choose n : ℝ)*A*B := by
    intro n hn
    by_cases hz : n=0
    · subst n
      simp [norm_iteratedFDeriv_zero]
    · rw [ite_eq_right hz,jet_sub_value hz f x (hf.of_le (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hn)))]
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (hfj n (by omega) (Nat.le_of_lt_succ (Finset.mem_range.mp hn))) (Nat.cast_nonneg _))
        (hgj (4-n) (by omega)) (norm_nonneg _) (by positivity)
  apply hb.trans
  calc
    _≤∑ n∈Finset.range 5, if n=0 then 0 else ((4:ℕ).choose n : ℝ)*A*B := Finset.sum_le_sum hs
    _=15*A*B := by norm_num [Finset.sum_range_succ,Nat.choose]; ring
lemma commutator_sub_left (f h : V → ℝ) (g : V → E) (x : V)
    (hf : ContDiff ℝ 4 f) (hh : ContDiff ℝ 4 h) (hg : ContDiff ℝ 4 g) :
    commutator (f-h) g x=commutator f g x-commutator h g x := by
  have he : (fun y => (f-h) y • g y)=(fun y => f y • g y)-(fun y => h y • g y) := by
    funext y; exact sub_smul _ _ _
  unfold commutator
  rw [he,iteratedFDeriv_sub (f := fun y => f y • g y) (g := fun y => h y • g y) (hf.smul hg) (hh.smul hg)]
  simp only [Pi.sub_apply,sub_smul]
  abel
lemma commutator_sub_right (f : V → ℝ) (g h : V → E) (x : V)
    (hf : ContDiff ℝ 4 f) (hg : ContDiff ℝ 4 g) (hh : ContDiff ℝ 4 h) :
    commutator f (g-h) x=commutator f g x-commutator f h x := by
  have he : (fun y => f y • (g-h) y)=(fun y => f y • g y)-(fun y => f y • h y) := by
    funext y; exact smul_sub _ _ _
  unfold commutator
  rw [he,iteratedFDeriv_sub (f := fun y => f y • g y) (g := fun y => f y • h y) (hf.smul hg) (hf.smul hh)]
  simp only [Pi.sub_apply,iteratedFDeriv_sub hg hh,smul_sub]
  abel
lemma commutator_translate (f : V → ℝ) (g : V → E) (x y : V) :
    commutator (fun z => f (z+y)) (fun z => g (z+y)) x=commutator f g (x+y) := by
  unfold commutator
  rw [iteratedFDeriv_comp_add_right (f := fun z => f z • g z),
    iteratedFDeriv_comp_add_right]
end ParabolicCommutator

end

end OAI
