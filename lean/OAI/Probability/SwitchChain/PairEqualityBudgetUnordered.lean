import OAI.Probability.SwitchChain.PairEqualityBudget
import OAI.Probability.SwitchChain.PairEqualityUnorderedSum
import OAI.Probability.SwitchChain.CrossToggleGain

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem orderedGain_eq_gain (i j k l : Fin n) :
    orderedGain (d := d) i j k l = CrossToggle.gain {i,j} {k,l} :=
  (CrossToggle.gain_pair_eq_ordered i j k l).symm

theorem gain_diag_right (a : Finset (Fin n)) (k : Fin n) :
    CrossToggle.gain (d := d) a {k,k} = 0 := by
  simp [CrossToggle.gain]

theorem sum_gain_eq_half_ordered (i j : Fin n) (f : StateSpace n d) :
    (∑ b ∈ pairs n, ‖CrossToggle.gain {i,j} b f‖ ^ 2) =
      (1 / 2 : ℝ) * ∑ k : Fin n, ∑ l : Fin n, ‖orderedGain i j k l f‖ ^ 2 := by
  have h := UnorderedPairSums.sum_ordered_eq_two_mul
    (fun b : Finset (Fin n) => ‖CrossToggle.gain {i,j} b f‖ ^ 2)
  have he (k l : Fin n) :
      (if k ≠ l then ‖CrossToggle.gain {i,j} {k,l} f‖ ^ 2 else 0) =
        ‖orderedGain i j k l f‖ ^ 2 := by
    rw [orderedGain_eq_gain]
    by_cases hkl : k ≠ l
    · rw [ite_eq_left hkl]
    · have hkl' : k = l := not_ne_iff.mp hkl
      subst l
      simp [CrossToggle.gain]
  simp_rw [he] at h
  change (∑ b ∈ (Finset.univ : Finset (Fin n)).powersetCard 2,
    ‖CrossToggle.gain {i,j} b f‖ ^ 2) = _
  linarith

theorem pair_projection_budget (a : Finset (Fin n)) (f : StateSpace n d) :
    (∑ b ∈ pairs n, ‖pairProjection a b f‖ ^ 2) ≤
      ∑ b ∈ pairs n, ‖CrossToggle.gain a b f‖ ^ 2 := by
  by_cases ha : a.card = 2
  · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp ha
    rw [sum_pairProjection_eq_half_ordered i j hij f, sum_gain_eq_half_ordered i j f]
    have h := ordered_projection_budget i j hij f
    have he (k l : Fin n) :
        (if k ≠ l then ‖projection i j k l f‖ ^ 2 else 0) =
        if k = l then 0 else ‖projection i j k l f‖ ^ 2 := by
      by_cases hkl : k = l <;> simp [hkl]
    simp_rw [he]
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  · have hz (b : Finset (Fin n)) : pairProjection (d := d) a b = 0 :=
      pairProjection_eq_zero_left a b ha
    simp only [hz, zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero]
    exact Finset.sum_nonneg (fun b _ => sq_nonneg _)

theorem sum_gain_norm_sq (a : Finset (Fin n)) (s : Finset (Finset (Fin n)))
    (f : StateSpace n d) :
    (∑ b ∈ s, if Disjoint a b then ‖CrossToggle.gain a b f‖ ^ 2 else 0) =
      ∑ b ∈ s, ‖CrossToggle.gain a b f‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : Disjoint a b
  · rw [ite_eq_left hab]
  · rw [ite_eq_right hab, CrossToggle.gain_eq_zero_of_not_disjoint a b hab]
    simp

theorem disjoint_pair_projection_budget (a : Finset (Fin n)) (f : StateSpace n d) :
    (∑ b ∈ pairs n, if Disjoint a b then ‖pairProjection a b f‖ ^ 2 else 0) ≤
      ∑ b ∈ pairs n, if Disjoint a b then ‖CrossToggle.gain a b f‖ ^ 2 else 0 := by
  rw [sum_pairProjection_norm_sq, sum_gain_norm_sq]
  exact pair_projection_budget a f

end Problem315.PairEquality

end

end OAI
