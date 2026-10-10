import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.TestRowEmpty

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory ProbabilityTheory SharpLogRamsey.PoissonSchedules
open scoped BigOperators Classical NNReal
noncomputable section
variable {A : Type*}

lemma sample_card_le_total (S : Finset A) (R : ℕ) (ω : Schedule S R) :
    (sample S ω).card≤∑ i : Fin R×S,ω i := by
  have hs (x : A) (hx : x∈sample S ω) : 1≤∑ r,extend S ω r x := by
    obtain ⟨r,hr⟩ := (mem_filter.mp hx).2
    have hh := single_le_sum (fun r _ => Nat.zero_le (extend S ω r x)) (mem_univ r)
    exact (Nat.one_le_iff_ne_zero.mpr hr).trans hh
  calc
    _ = ∑ x∈sample S ω,1 := by simp
    _ ≤ ∑ x∈sample S ω,∑ r,extend S ω r x := sum_le_sum hs
    _ ≤ ∑ x∈S,∑ r,extend S ω r x :=
      sum_le_sum_of_subset_of_nonneg (sample_subset S ω) (fun _ _ _ => Nat.zero_le _)
    _ = ∑ x : S,∑ r,ω (r,x) := by
      rw [←sum_coe_sort S (fun x : A => ∑ r,extend S ω r x)]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro r _
      exact dite_eq_left x.2
    _ = ∑ i : Fin R×S,ω i := by rw [Fintype.sum_prod_type,sum_comm]

lemma constant_mean (S : Finset A) (R : ℕ) (γ : ℝ≥0) :
    (∑ _i : Fin R×S,(γ:ℝ))=(R:ℝ)*S.card*γ := by
  simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_coe,
    nsmul_eq_mul,Nat.cast_mul]

theorem sample_size_tail (S : Finset A) (R : ℕ) (γ : ℝ≥0) :
    (scheduleLaw (fun _ : Fin R×S => γ)).real
      {ω | 2*((R:ℝ)*S.card*γ)<((sample S ω).card:ℝ)}≤
        Real.exp (-((R:ℝ)*S.card*γ)/3) := by
  have hh := SharpLogRamsey.PoissonTail.total_tail (fun _ : Fin R×S => γ)
  rw [constant_mean S R γ] at hh
  apply le_trans (measureReal_mono (h₂:=measure_ne_top _ _) ?_) hh
  intro ω hω
  change 2*((R:ℝ)*S.card*γ)<((sample S ω).card:ℝ) at hω
  change 2*((R:ℝ)*S.card*γ)≤((∑ i : Fin R×S,ω i : ℕ):ℝ)
  exact hω.le.trans (Nat.cast_le.mpr (sample_card_le_total S R ω))

end
end SharpLogRamsey.PreparedRow

end

end OAI
