import OAI.NumberTheory.JointDickman.Arithmetic.ConsecutivePrimeHits

namespace OAI

/-! # Reindexing two prime-hit vectors as two prime subsets -/

namespace JointDickman
open Finset

noncomputable def pairHitEquiv (P : Finset ℕ) :
    (P.powerset × P.powerset) ≃ (P → Bool × Bool) where
  toFun S p := (subsetHitEquiv P S.1 p, subsetHitEquiv P S.2 p)
  invFun x := ((subsetHitEquiv P).symm (fun p => (x p).1),
    (subsetHitEquiv P).symm (fun p => (x p).2))
  left_inv S := by simp
  right_inv x := by
    funext p
    exact Prod.ext
      (congrFun ((subsetHitEquiv P).apply_symm_apply (fun p => (x p).1)) p)
      (congrFun ((subsetHitEquiv P).apply_symm_apply (fun p => (x p).2)) p)

noncomputable def hitSites (P : Finset ℕ) (x : P → Bool × Bool) : P.powerset × P.powerset :=
  (pairHitEquiv P).symm x

theorem pairHitMass_eq (P : Finset ℕ) (q : ℕ → ℝ) (S D : P.powerset) :
    finiteProductMass (fun p : P => independentHitMass (q p.val)) (pairHitEquiv P (S,D)) =
      bernoulliSubsetMass P q S.val * bernoulliSubsetMass P q D.val := by
  change (∏ p : P, bernoulliBitMass (q p.val) (subsetHitEquiv P S p) *
    bernoulliBitMass (q p.val) (subsetHitEquiv P D p)) = _
  rw [prod_mul_distrib]
  exact congrArg₂ (· * ·) (bernoulliSubsetMass_eq_product P q S)
    (bernoulliSubsetMass_eq_product P q D)

theorem pairHitSites_sum (P : Finset ℕ) (q : ℕ → ℝ) (F : Finset ℕ → Finset ℕ → ℝ) :
    (∑ x, finiteProductMass (fun p : P => independentHitMass (q p.val)) x *
      F (hitSites P x).1.val (hitSites P x).2.val) =
      ∑ S ∈ P.powerset, ∑ D ∈ P.powerset,
        bernoulliSubsetMass P q S * bernoulliSubsetMass P q D * F S D := by
  rw [← (pairHitEquiv P).sum_comp]
  simp only [hitSites, Equiv.symm_apply_apply, Fintype.sum_prod_type, pairHitMass_eq]
  calc
    _ = ∑ S : P.powerset, ∑ D ∈ P.powerset,
        bernoulliSubsetMass P q S.val * bernoulliSubsetMass P q D * F S.val D := by
      apply sum_congr rfl
      intro S _
      exact P.powerset.sum_coe_sort (fun D =>
        bernoulliSubsetMass P q S.val * bernoulliSubsetMass P q D * F S.val D)
    _ = _ := P.powerset.sum_coe_sort (fun S => ∑ D ∈ P.powerset,
      bernoulliSubsetMass P q S * bernoulliSubsetMass P q D * F S D)

theorem hitSites_consecutive (P : Finset ℕ) (n : ℕ) :
    hitSites P (fun p => consecutivePrimeHit (n : ZMod p.val)) =
      (⟨P.filter (fun p => p ∣ n), mem_powerset.mpr (filter_subset _ _)⟩,
       ⟨P.filter (fun p => p ∣ n+1), mem_powerset.mpr (filter_subset _ _)⟩) := by
  apply (pairHitEquiv P).injective
  rw [show pairHitEquiv P (hitSites P (fun p => consecutivePrimeHit (n : ZMod p.val))) =
      (fun p => consecutivePrimeHit (n : ZMod p.val)) from (pairHitEquiv P).apply_symm_apply _]
  funext p
  apply Prod.ext
  · simp [pairHitEquiv, subsetHitEquiv, consecutivePrimeHit, p.property, ZMod.natCast_eq_zero_iff]
  · have he : (n : ZMod p.val) = -1 ↔ p.val ∣ n+1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      simp only [Nat.cast_add, Nat.cast_one, add_eq_zero_iff_eq_neg]
    simp [pairHitEquiv, subsetHitEquiv, consecutivePrimeHit, p.property, he]

end JointDickman

end OAI
