import OAI.NumberTheory.CubicMoment.Decomposition.StoppingProductSlice

namespace OAI

/-! Exact collection of the distinguished subset expansion by its
primary product. The original finite support remains inside each row. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedSubsetWeight (ψ : ℝ → ℝ) (w z : ℝ) (r : Eisenstein) : ℂ :=
  ∏ p ∈ primaryPrimeFactors r, distinguishedPrimeWeight ψ w z p

theorem roughProduct_distinguished_primary_pairs {n : Eisenstein}
    (hn : primary n) (hs : Squarefree n) {X : ℝ} (hnX : norm n ≤ X)
    (ψ : ℝ → ℝ) (w z : ℝ) :
    (roughProduct ψ z n:ℂ) =
      ∑ q ∈ ((primaryElementBall X).product (primaryElementBall X)).filter
          (fun q => q.1*q.2 = n),
        distinguishedSubsetWeight ψ w z q.1*(roughProduct ψ w q.2:ℂ) := by
  rw [←squarefree_primary_factor_pairs hn hs hnX
    (fun r u => distinguishedSubsetWeight ψ w z r*(roughProduct ψ w u:ℂ)),
    roughProduct_ordered_primary_tuples hn]
  simp_rw [ordered_subset_product]
  apply Finset.sum_congr rfl
  intro s hsub
  rw [distinguishedSubsetWeight,primaryPrimeFactors_finset_prod s
    (fun p hp => (primaryPrimeFactor_spec hn (Finset.mem_powerset.mp hsub hp)).1)]
  rfl

theorem roughProduct_distinguished_finite_pairs (S : Finset Eisenstein) (X : ℝ)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (ψ : ℝ → ℝ) (w z : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ S, (roughProduct ψ z n:ℂ)*K n) =
      ∑ r ∈ primaryElementBall X, ∑ u ∈ primaryElementBall X,
        if r*u ∈ S then
          distinguishedSubsetWeight ψ w z r*(roughProduct ψ w u:ℂ)*K (r*u)
        else 0 := by
  calc
    _ = ∑ n ∈ S,
        ∑ q ∈ ((primaryElementBall X).product (primaryElementBall X)).filter
            (fun q => q.1*q.2 = n),
          distinguishedSubsetWeight ψ w z q.1*(roughProduct ψ w q.2:ℂ)*K (q.1*q.2) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [roughProduct_distinguished_primary_pairs (hS n hn).1 (hS n hn).2.1
        (hS n hn).2.2 ψ w z,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      rw [(Finset.mem_filter.mp hq).2]
    _ = _ := primary_pair_fiber_support S X
      (fun r u => distinguishedSubsetWeight ψ w z r*(roughProduct ψ w u:ℂ)*K (r*u))

/-- The exact original rough weight is a sum of its distinguished rows,
with the sharp product support retained in each row. -/
theorem roughProduct_distinguished_slices (S : Finset Eisenstein) (X : ℝ)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    (ψ : ℝ → ℝ) (w z : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ S, (roughProduct ψ z n:ℂ)*K n) =
      ∑ r ∈ primaryElementBall X, distinguishedSubsetWeight ψ w z r*
        ∑ u ∈ primaryProductSlice S X r, (roughProduct ψ w u:ℂ)*K (r*u) := by
  rw [roughProduct_distinguished_finite_pairs S X hS ψ w z K]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [primaryProductSlice,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _hu
  split_ifs <;> simp [mul_assoc]

end CubicFirstMoment

end

end OAI
