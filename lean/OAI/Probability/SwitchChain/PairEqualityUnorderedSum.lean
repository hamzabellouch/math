import OAI.Probability.SwitchChain.PairEqualityUnordered
import OAI.Probability.SwitchChain.UnorderedPairSums

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem projection_diag_right (i j k : Fin n) :
    projection (d := d) i j k k = 0 := by
  have hz : centered (d := d) i j k k = 0 := by
    unfold centered
    apply (fluctuation_eq_zero_iff _ _).mpr
    intro G H h
    change (if G.val.Adj i k ↔ G.val.Adj i k then (1 : ℝ) else 0) =
      if H.val.Adj i k ↔ H.val.Adj i k then 1 else 0
    simp
  have he : equalitySpace (d := d) i j k k = ⊥ := by
    apply le_antisymm
    · intro f hf
      change f = 0
      ext G
      change f G = 0
      obtain ⟨c,hc⟩ := hf G
      have h := hc G (SameFiber.refl _ _)
      simpa only [hz, PiLp.zero_apply, ite_self, mul_zero] using h
    · exact bot_le
  exact (congrArg (fun M : Submodule ℝ (StateSpace n d) => M.starProjection) he).trans
    Submodule.starProjection_bot

theorem sum_pairProjection_eq_half_ordered (i j : Fin n) (hij : i ≠ j)
    (f : StateSpace n d) :
    (∑ b ∈ pairs n, ‖pairProjection {i,j} b f‖ ^ 2) =
      (1 / 2 : ℝ) * ∑ k : Fin n, ∑ l : Fin n,
        if k ≠ l then ‖projection i j k l f‖ ^ 2 else 0 := by
  have h := UnorderedPairSums.sum_ordered_eq_two_mul
    (fun b : Finset (Fin n) => ‖pairProjection {i,j} b f‖ ^ 2)
  have he (k l : Fin n) :
      (if k ≠ l then ‖pairProjection {i,j} {k,l} f‖ ^ 2 else 0) =
        if k ≠ l then ‖projection i j k l f‖ ^ 2 else 0 := by
    by_cases hkl : k ≠ l
    · rw [ite_eq_left hkl, ite_eq_left hkl, pairProjection_pair i j k l hij hkl]
    · rw [ite_eq_right hkl, ite_eq_right hkl]
  simp_rw [he] at h
  change (∑ b ∈ (Finset.univ : Finset (Fin n)).powersetCard 2,
    ‖pairProjection {i,j} b f‖ ^ 2) = _
  linarith

theorem sum_disjoint_pairProjection_eq_half_ordered (i j : Fin n) (hij : i ≠ j)
    (f : StateSpace n d) :
    (∑ b ∈ pairs n,
      if Disjoint ({i,j} : Finset (Fin n)) b then
        ‖pairProjection {i,j} b f‖ ^ 2 else 0) =
      (1 / 2 : ℝ) * ∑ k : Fin n, ∑ l : Fin n,
        if k ≠ l then ‖projection i j k l f‖ ^ 2 else 0 := by
  rw [sum_pairProjection_norm_sq, sum_pairProjection_eq_half_ordered i j hij f]

theorem sum_pairProjection_eq_half_full (i j : Fin n) (hij : i ≠ j)
    (f : StateSpace n d) :
    (∑ b ∈ pairs n, ‖pairProjection {i,j} b f‖ ^ 2) =
      (1 / 2 : ℝ) * ∑ k : Fin n, ∑ l : Fin n, ‖projection i j k l f‖ ^ 2 := by
  rw [sum_pairProjection_eq_half_ordered i j hij f]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hkl : k ≠ l
  · rw [ite_eq_left hkl]
  · have he : k = l := not_ne_iff.mp hkl
    subst l
    simp [projection_diag_right]

end Problem315.PairEquality

end

end OAI
