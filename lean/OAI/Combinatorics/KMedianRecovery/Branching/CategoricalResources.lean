import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Score
import OAI.Combinatorics.KMedianRecovery.Branching.CategoricalRule

namespace OAI

namespace MetricKMedianRecovery.Categorical.Explicit
open FiniteSampling

def exponent (a : ℕ) : ℕ := 2*(a+1).size+10
def steps (a : ℕ) : ℕ := 2^exponent a
def samples (q a : ℕ) : ℕ := 1000000000*steps a*(q+1)*(a+1)^2
lemma pow_size_bound (n : ℕ) : 2^n.size ≤ 2*(n+1) := by
  by_cases hn : n=0
  · subst n; norm_num
  · have hp : 0<n.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
    have hh:=Nat.lt_size.mp (show n.size-1<n.size by omega)
    have he : n.size=n.size-1+1 := by omega
    rw [he,pow_succ]
    omega
lemma steps_pos (a : ℕ) : 0<steps a := pow_pos (by decide) _
lemma steps_lower (a : ℕ) : 1000*(a+1)^2 ≤ steps a := by
  have hh : a+1 ≤ 2^(a+1).size := (Nat.lt_size_self _).le
  have hs := Nat.pow_le_pow_left hh 2
  unfold steps exponent
  rw [pow_add,show 2*(a+1).size=(a+1).size*2 by omega,pow_mul]
  norm_num
  nlinarith
lemma steps_upper (a : ℕ) : steps a ≤ 4096*(a+2)^2 := by
  have hh := pow_size_bound (a+1)
  have hs:=Nat.pow_le_pow_left hh 2
  unfold steps exponent
  rw [pow_add,show 2*(a+1).size=(a+1).size*2 by omega,pow_mul]
  norm_num
  nlinarith
lemma samples_pos (q a : ℕ) : 0<samples q a := by unfold samples; have := steps_pos a; positivity
lemma scale (a : ℕ) : (a:ℝ)^2 ≤ (1/1000:ℝ)*steps a := by
  have hh : (1000:ℝ)*(a+1)^2 ≤ steps a := by exact_mod_cast steps_lower a
  have ha : (0:ℝ) ≤ a := Nat.cast_nonneg a
  nlinarith
attribute [local irreducible] steps exponent
lemma count (q a : ℕ) : ((steps a:ℕ):ℝ)*q*a^2/(4*(1/1000:ℝ)^3) ≤ samples q a := by
  unfold samples
  push_cast
  have ht : (0:ℝ) ≤ steps a := Nat.cast_nonneg _
  have hq : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have ha : (0:ℝ) ≤ a := Nat.cast_nonneg _
  have hsq : (a:ℝ)^2 ≤ (a+1)^2 := by nlinarith
  have hh : (steps a:ℝ)*q*a^2 ≤ steps a*(q+1)*(a+1)^2 := by gcongr; linarith
  calc
    _ = 250000000*((steps a:ℝ)*q*a^2) := by ring
    _ ≤ 250000000*(steps a*(q+1)*(a+1)^2) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ ≤ _ := by
      have hn : (0:ℝ) ≤ steps a*(q+1)*(a+1)^2 := by positivity
      nlinarith

attribute [local irreducible] samples
lemma sixtyTwo {E : Type*} [Fintype E] [DecidableEq E] {a : ℕ}
    (part : E→Fin a) (rule : Selected.Rule part) (g : SetFunction E)
    (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅=0)
    (S : Finset E) (hS : PartitionFeasible part S) :
    (62/100:ℝ)*g S ≤ average (fun bits : BinaryOracleIndex E a (exponent a) (samples (Fintype.card E) a)→Bool =>
      g (Selected.binaryGreedyOutput part rule g bits)) := by
  by_cases ha : 0<a
  · have hh:=Selected.binaryGreedyOutput_expected (b:=exponent a) (L:=samples (Fintype.card E) a) part rule g hmono hsub hg0 ha
      (show (0:ℝ)<1/1000 by norm_num) (by norm_num) (by simpa only [steps] using scale a)
      (samples_pos (Fintype.card E) a) (by simpa only [steps] using count (Fintype.card E) a) S hS
    have he : 1/Real.exp 1 ≤ (37/100:ℝ) := by
      rw [div_le_iff₀ (Real.exp_pos 1)]
      linarith [Real.exp_one_gt_d9]
    have hn : 0 ≤ g S := by rw [←hg0]; exact hmono (Finset.empty_subset _)
    exact (mul_le_mul_of_nonneg_right (by linarith : (62/100:ℝ) ≤ 1-1/Real.exp 1-4*(1/1000)) hn).trans hh
  · have hE : IsEmpty E := ⟨fun e=>by have := (part e).isLt; omega⟩
    have hS0 : S=∅ := Subsingleton.elim _ _
    rw [hS0,hg0,mul_zero]
    apply average_nonneg
    intro bits
    rw [Subsingleton.elim (Selected.binaryGreedyOutput part rule g bits) ∅,hg0]
end MetricKMedianRecovery.Categorical.Explicit

namespace MetricKMedianRecovery.Completion.Explicit
open Categorical FiniteSampling
variable {E P R : Type*} [Fintype E] [DecidableEq E] [Fintype P] [Fintype R]
lemma expected {a : ℕ} (part : E→Fin a) (rule : Categorical.Selected.Rule part)
    (K : ℝ) (q : ℕ) (base : P→ℝ) (distance : P→E→ℝ)
    (weight redBase : R→ℝ) (redDistance : R→E→ℝ) (hw : ∀ r,0≤weight r)
    (S : Finset E) (hS : PartitionFeasible part S) :
    average (fun bits : BinaryOracleIndex E a (Categorical.Explicit.exponent a)
      (Categorical.Explicit.samples (Fintype.card E) a)→Bool =>
        surrogate K q base distance weight redBase redDistance
          (Categorical.Selected.binaryGreedyOutput part rule (saving K q base distance weight redBase redDistance) bits)) ≤
      (38/100:ℝ)*surrogate K q base distance weight redBase redDistance ∅+
        (62/100:ℝ)*surrogate K q base distance weight redBase redDistance S := by
  have hh:=Categorical.Explicit.sixtyTwo part rule (saving K q base distance weight redBase redDistance)
    (saving_mono K q base distance weight redBase redDistance hw)
    (fun X Y hXY e=>saving_diminishing K q base distance weight redBase redDistance hw hXY e)
    (saving_empty K q base distance weight redBase redDistance) S hS
  simp only [saving,average_sub,average_const] at hh
  linarith
end MetricKMedianRecovery.Completion.Explicit

end OAI
