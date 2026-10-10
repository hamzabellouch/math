import OAI.NumberTheory.JointDickman.Arithmetic.BrunTruncationError
import OAI.NumberTheory.JointDickman.Arithmetic.RequiredPrimeSubset

namespace OAI

/-! # The finite-population upper sieve from an even truncation -/
namespace JointDickman
open Finset

 theorem brunTruncation_inter (P E : Finset ℕ) (m : ℕ) :
    brunTruncation (P ∩ E) m = ∑ D ∈ P.powerset.filter (fun D => D.card ≤ m),
      if D ⊆ E then (-1 : ℝ)^D.card else 0 := by
  classical
  rw [brunTruncation, ← sum_filter]
  apply sum_congr
  · ext D
    simp only [mem_filter, mem_powerset, subset_inter_iff]
    tauto
  · intros; rfl

 theorem brunMean_eq (P : Finset ℕ) (g : ℕ → ℝ) (r : ℕ) :
    brunMean P g r = ∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2*r),
      (-1 : ℝ)^D.card * ∏ p ∈ D, g p := by
  classical
  have he (E : Finset ℕ) (hE : E ∈ P.powerset) : E = P ∩ E := by
    symm
    exact inter_eq_right.mpr (mem_powerset.mp hE)
  have hexp (E : Finset ℕ) (hE : E ∈ P.powerset) : brunTruncation E (2*r) =
      ∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2*r),
        if D ⊆ E then (-1 : ℝ)^D.card else 0 :=
    (congrArg (fun T => brunTruncation T (2*r)) (he E hE)).trans (brunTruncation_inter P E (2*r))
  unfold brunMean
  rw [sum_congr rfl (fun E hE => congrArg (fun t => bernoulliSubsetMass P g E*t) (hexp E hE))]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro D hD
  calc
    _ = (-1 : ℝ)^D.card * ∑ E ∈ P.powerset,
        if D ⊆ E then bernoulliSubsetMass P g E else 0 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro E _
      split_ifs <;> ring
    _ = _ := by rw [bernoulliSubsetMass_required P D g (mem_powerset.mp (mem_filter.mp hD).1)]

 theorem brunTruncation_population_sum {X : Type*} [Fintype X]
    (P : Finset ℕ) (E : X → Finset ℕ) (w : X → ℝ) (r : ℕ) :
    (∑ x, w x * brunTruncation (P ∩ E x) (2*r)) =
      ∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2*r),
        (-1 : ℝ)^D.card * sieveIntersection E w D := by
  classical
  simp_rw [brunTruncation_inter, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro D _
  rw [sieveIntersection, mul_sum]
  apply sum_congr rfl
  intro x _
  split_ifs <;> ring

 theorem brun_population_bound {X : Type*} [Fintype X]
    (P : Finset ℕ) (E : X → Finset ℕ) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (M : ℝ) (g : ℕ → ℝ) (r : ℕ) :
    (∑ x, w x * avoidsSelected P (E x)) ≤ M*brunMean P g r +
      ∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2*r), |sieveRemainder E w M g D| := by
  classical
  calc
    _ ≤ ∑ x, w x*brunTruncation (P ∩ E x) (2*r) :=
      sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (brunTruncation_upper P (E x) r) (hw x))
    _ = M*brunMean P g r + ∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2*r),
        (-1 : ℝ)^D.card*sieveRemainder E w M g D := by
      rw [brunTruncation_population_sum, brunMean_eq, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro D _
      rw [sieveRemainder]
      ring
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply sum_le_sum
      intro D _
      calc
        _ ≤ |(-1 : ℝ)^D.card*sieveRemainder E w M g D| := le_abs_self _
        _ = _ := by rw [abs_mul, abs_pow]; norm_num

end JointDickman

end OAI
