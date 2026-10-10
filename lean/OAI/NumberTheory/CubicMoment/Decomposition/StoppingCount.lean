import OAI.NumberTheory.CubicMoment.Estimates.RoughMoebius

namespace OAI

/-! The actual first-crossing count in one prime bin. All subsets with
that count obey the same predicate, so inverse-binomial weighting is exact. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma first_bin_crossing {R ell Z : ℝ} (_hR : 0 < R) (hell : 1 < ell)
    (hstart : R < Z) {N : ℕ} (hend : Z ≤ R*ell^N) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧
      R*ell^k/ell < Z ∧ Z ≤ R*ell^k ∧ R*ell^k < ell*Z := by
  have hex : ∃ k : ℕ, Z ≤ R*ell^k := ⟨N,hend⟩
  let k := Nat.find hex
  have hhit : Z ≤ R*ell^k := Nat.find_spec hex
  have hk : 0 < k := by
    by_contra h
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
    rw [hk0,pow_zero,mul_one] at hhit
    exact (not_le_of_gt hstart) hhit
  have hprev : R*ell^(k-1) < Z :=
    lt_of_not_ge (Nat.find_min hex (Nat.sub_lt hk (by decide)))
  have hstep : R*ell^k = (R*ell^(k-1))*ell := by
    calc
      _ = R*ell^(k-1+1) := congrArg (fun m : ℕ => R*ell^m) (Nat.sub_add_cancel hk).symm
      _ = _ := by rw [pow_succ]; ring
  have hellp : 0 < ell := zero_lt_one.trans hell
  refine ⟨k,hk,Nat.find_min' hex hend,?_,hhit,?_⟩
  · rwa [hstep,mul_div_cancel_right₀ _ hellp.ne']
  · rw [hstep,mul_comm ell Z]
    exact mul_lt_mul_of_pos_right hprev hellp

/-- This is the source crossing predicate on the selected side, with
actual primary prime products and their actual cutoff-Möbius weights. -/
theorem first_bin_crossing_coefficient (ψ : ℝ → ℝ) (w : ℝ)
    (s : Finset Eisenstein) (hs : ∀ p ∈ s, primaryPrime p)
    {R ell Z : ℝ} (hR : 0 < R) (hell : 1 < ell) (hstart : R < Z)
    (hend : Z ≤ R*ell^s.card) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ s.card ∧
      (∑ t ∈ s.powersetCard k,
        if R*ell^t.card/ell < Z ∧ Z ≤ R*ell^t.card then
          (s.card.choose k:ℂ)⁻¹*
            (cutoffMoebius ψ w (∏ p ∈ t, p)*cutoffMoebius ψ w (∏ p ∈ s\t, p))
        else 0) = cutoffMoebius ψ w (∏ p ∈ s, p) := by
  obtain ⟨k,hk,hks,hprev,hhit,_hupper⟩ := first_bin_crossing hR hell hstart hend
  refine ⟨k,hk,hks,?_⟩
  calc
    _ = ∑ t ∈ s.powersetCard k, (s.card.choose k:ℂ)⁻¹*
      (cutoffMoebius ψ w (∏ p ∈ t, p)*cutoffMoebius ψ w (∏ p ∈ s\t, p)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [(Finset.mem_powersetCard.mp ht).2]
      simp only [hprev,hhit,and_self,ite_true]
    _ = _ := cutoffMoebius_stopping_bin ψ w s hs k hks

end CubicFirstMoment

end

end OAI
