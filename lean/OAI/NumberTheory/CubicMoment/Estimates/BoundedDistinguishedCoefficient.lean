import OAI.NumberTheory.CubicMoment.Estimates.PrimeTupleFiber
import OAI.NumberTheory.CubicMoment.Estimates.BoundedPrimeTuples

namespace OAI

/-! The actual distinguished subset coefficient is the finite sum of
its fixed-length prime convolutions. The arity cutoff is proved from the
lower bound on every prime carrying a nonzero distinguished weight. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma distinguishedSubsetWeight_eq_sum_tuples {n : Eisenstein}
    (hn : primary n) (hs : Squarefree n) {B : ℝ} (hB : norm n ≤ B)
    {ψ : ℝ → ℝ} (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z : ℝ} (hw : 1 ≤ w) (hwz : w ≤ z) {k : ℕ} (hsize : norm n < w^k) :
    distinguishedSubsetWeight ψ w z n =
      ∑ i ∈ Finset.range k,
        distinguishedTupleCoefficient (fun _ : Fin i => primeCutoff B)
          (fun _ _ => 1) ψ w z n := by
  let m := (primaryPrimeFactors n).card
  have hother (i : ℕ) (hi : i ≠ m) :
      distinguishedTupleCoefficient (fun _ : Fin i => primeCutoff B)
        (fun _ _ => 1) ψ w z n = 0 := by
    apply distinguishedTupleCoefficient_zero_of_card_ne hn hs
    simpa only [Fintype.card_fin] using hi
  by_cases hm : m < k
  · rw [Finset.sum_eq_single m]
    · exact distinguishedSubsetWeight_as_tuple hn hs hB ψ w z
    · intro i _hi him
      exact hother i him
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hm)).elim
  · have hz : distinguishedSubsetWeight ψ w z n = 0 := by
      by_contra hne
      exact hm (distinguished_subset_card_lt hn hs hψone hψzero hw hwz
        (Finset.Subset.refl _) hne hsize)
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    exact hother i (fun he => hm (he ▸ Finset.mem_range.mp hi))

theorem eventually_distinguished_coefficient_tuples {ξ C : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hC : 0 < C)
    {ψ : ℝ → ℝ} (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0) :
    ∃ k : ℕ, ∀ᶠ X : ℝ in atTop, ∀ n : Eisenstein,
      primary n → Squarefree n → norm n ≤ C*X →
      distinguishedSubsetWeight ψ (X^ξ) (X^(2/5:ℝ)) n =
        ∑ i ∈ Finset.range k,
          distinguishedTupleCoefficient (fun _ : Fin i => primeCutoff (C*X))
            (fun _ _ => 1) ψ (X^ξ) (X^(2/5:ℝ)) n := by
  obtain ⟨k,hk⟩ := exists_nat_gt (1/ξ)
  have hk' : 1 < ξ*(k:ℝ) := by
    have hh := (div_lt_iff₀ hξ).mp hk
    nlinarith
  refine ⟨k,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_prime_tuple_norm_bound hC hk']
    with X hX hsize
  intro n hn hs hnX
  exact distinguishedSubsetWeight_eq_sum_tuples hn hs hnX hψone hψzero
    (Real.one_le_rpow hX.le hξ.le) (Real.rpow_le_rpow_of_exponent_le hX.le hξz)
    (hnX.trans_lt hsize)

end CubicFirstMoment

end

end OAI
