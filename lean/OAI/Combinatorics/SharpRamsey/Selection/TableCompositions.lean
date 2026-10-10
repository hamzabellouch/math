import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.PivotValidation

namespace OAI

section
namespace SharpLogRamsey.PublicTables
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Ω : Type*} [Fintype Ω]

lemma integral_on_mono (p : Law Ω) (A : Ω→Prop) (f g : Ω→ℝ) (m : ℕ)
    (h : ∀ z,A z→f z≤ g z) : integral p A f m≤ integral p A g m := by
  apply sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_left _ (tableWeight_nonneg p m z)
  unfold outcome
  generalize he : first A m z = o
  cases o with
  | none => rfl
  | some x => exact h x (first_valid A m z x he)

lemma integral_const (p : Law Ω) (A : Ω→Prop) (c : ℝ) (m : ℕ) :
    integral p A (fun _ => c) m=c*integral p A (fun _ => 1) m := by
  have ho (z : Table Ω m) : outcome A (fun _ => c) m z=c*outcome A (fun _ => 1) m z := by
    unfold outcome
    cases first A m z <;> simp
  simp only [integral,ho,mul_sum]
  apply sum_congr rfl
  intro z _
  ring

lemma integral_sub (p : Law Ω) (A : Ω→Prop) (f g : Ω→ℝ) (m : ℕ) :
    integral p A (fun z => f z-g z) m=integral p A f m-integral p A g m := by
  have ho (z : Table Ω m) : outcome A (fun z => f z-g z) m z=
      outcome A f m z-outcome A g m z := by
    unfold outcome
    cases first A m z <;> simp
  simp only [integral,ho,mul_sub,sum_sub_distrib]

lemma integral_one_nonneg (p : Law Ω) (A : Ω→Prop) (m : ℕ) :
    0≤ integral p A (fun _ => 1) m := by
  apply sum_nonneg
  intro z _
  apply mul_nonneg (tableWeight_nonneg p m z)
  unfold outcome
  cases first A m z <;> norm_num

lemma integral_one_le (p : Law Ω) (A : Ω→Prop) (m : ℕ) :
    integral p A (fun _ => 1) m≤1 := by
  calc
    _ ≤ ∑ z,tableWeight p m z := ?_
    _ = 1 := tableWeight_total p m
  apply sum_le_sum
  intro z _
  have ho : outcome A (fun _ => 1) m z≤1 := by
    unfold outcome
    cases first A m z <;> norm_num
  simpa only [mul_one] using mul_le_mul_of_nonneg_left ho (tableWeight_nonneg p m z)

theorem integral_bounded (p : Law Ω) (A : Ω→Prop) (f : Ω→ℝ) (m : ℕ)
    (B : ℝ) (hB : 0≤ B) (hf : ∀ z,A z→f z≤ B) : integral p A f m≤ B := by
  apply (integral_on_mono p A f (fun _ => B) m hf).trans
  rw [integral_const]
  exact (mul_le_mul_of_nonneg_left (integral_one_le p A m) hB).trans_eq (mul_one B)

theorem two_stage_failure (p : Law Ω) (A : Ω→Prop) (next : Ω→ℝ) (m : ℕ)
    (δ δ' : ℝ) (hδ' : 0≤δ')
    (hfirst : 1-integral p A (fun _ => 1) m≤δ)
    (hnext : ∀ z,A z→1-next z≤δ') :
    1-integral p A next m≤δ+δ' := by
  have hh := integral_bounded p A (fun z => 1-next z) m δ' hδ' hnext
  rw [integral_sub] at hh
  linarith

end
end SharpLogRamsey.PublicTables

end

end OAI
