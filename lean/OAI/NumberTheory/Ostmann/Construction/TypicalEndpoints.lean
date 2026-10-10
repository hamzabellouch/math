import Mathlib.Algebra.BigOperators.Field
import OAI.NumberTheory.Ostmann.Construction.CollisionTestTransfer

namespace OAI

/-! # Few endpoints fail a positive prime test

The argument tests the uniform measure on the actual exceptional set. This
turns the collision estimate for every large subset into a cardinality bound.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem weighted_real_sum_sq {ι : Type*} (S : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    (∑ i ∈ S, w i * f i) ^ 2 ≤ (∑ i ∈ S, w i) * ∑ i ∈ S, w i * f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * f i)
  have h1 : (∑ i ∈ S, Real.sqrt (w i) * (Real.sqrt (w i) * f i)) =
      ∑ i ∈ S, w i * f i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hw i hi)]
  have h2 : (∑ i ∈ S, Real.sqrt (w i) ^ 2) = ∑ i ∈ S, w i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.sq_sqrt (hw i hi)
  have h3 : (∑ i ∈ S, (Real.sqrt (w i) * f i) ^ 2) = ∑ i ∈ S, w i * f i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rwa [h1, h2, h3] at h

theorem weighted_mean_commute (E P : Finset ℕ) (w : ℕ → ℝ) (f : ℕ → ℕ → ℝ) :
    (∑ p ∈ P, w p * residueTestMean E (fun a => f a p)) =
      residueTestMean E (fun a => ∑ p ∈ P, w p * f a p) := by
  unfold residueTestMean
  simp_rw [← mul_div_assoc, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]

noncomputable def badEndpoints (A P : Finset ℕ) (w : ℕ → ℝ)
    (f : ℕ → ℕ → ℝ) (δ : ℝ) : Finset ℕ :=
  A.filter (fun a => (∑ p ∈ P, w p * f a p) < (δ / 2) * ∑ p ∈ P, w p)

/-- No large subset can consist entirely of endpoints whose weighted mean
is less than half the positive reference mean. -/
theorem badEndpoints_card_lt (A P : Finset ℕ) (w g : ℕ → ℝ)
    (f : ℕ → ℕ → ℝ) (δ E : ℝ) (K : ℕ) (hK : 0 < K) (hδ : 0 < δ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (hmass : 0 < ∑ p ∈ P, w p)
    (href : δ * (∑ p ∈ P, w p) ≤ ∑ p ∈ P, w p * g p)
    (hsmall : 4 * E < δ ^ 2 * ∑ p ∈ P, w p)
    (htest : ∀ B ⊆ A, K ≤ B.card →
      (∑ p ∈ P, w p * (residueTestMean B (fun a => f a p) - g p) ^ 2) ≤ E) :
    (badEndpoints A P w f δ).card < K := by
  by_contra! hbad
  let B := badEndpoints A P w f δ
  have hB : B.Nonempty := Finset.card_pos.mp (hK.trans_le hbad)
  have hBc : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hsum : (∑ a ∈ B, ∑ p ∈ P, w p * f a p) <
      (B.card : ℝ) * ((δ / 2) * ∑ p ∈ P, w p) := by
    calc
      _ < ∑ _a ∈ B, ((δ / 2) * ∑ p ∈ P, w p) :=
        Finset.sum_lt_sum_of_nonempty hB (fun a ha => (Finset.mem_filter.mp ha).2)
      _ = _ := by simp
  have hmean : (∑ p ∈ P, w p * residueTestMean B (fun a => f a p)) <
      (δ / 2) * ∑ p ∈ P, w p := by
    rw [weighted_mean_commute, residueTestMean]
    exact (div_lt_iff₀ hBc).mpr (by nlinarith only [hsum])
  let e := fun p => residueTestMean B (fun a => f a p) - g p
  have he : (∑ p ∈ P, w p * e p) < -(δ / 2) * ∑ p ∈ P, w p := by
    simp only [e, mul_sub, Finset.sum_sub_distrib]
    linarith
  have hsquare := weighted_real_sum_sq P w e hw
  have htestB := htest B (Finset.filter_subset _ _) hbad
  have hupper := mul_le_mul_of_nonneg_left htestB hmass.le
  change (∑ p ∈ P, w p) * (∑ p ∈ P, w p * e p ^ 2) ≤ _ at hupper
  have hlo : (δ * (∑ p ∈ P, w p)) ^ 2 / 4 < (∑ p ∈ P, w p * e p) ^ 2 := by
    nlinarith [mul_pos hδ hmass]
  have hsmall' := mul_lt_mul_of_pos_left hsmall hmass
  nlinarith

/-- Finitely many prime tests hold simultaneously after deleting at most
the sum of their exceptional-set bounds. -/
theorem simultaneous_good_endpoints {ι : Type*} [DecidableEq ι]
    (E : Finset ℕ) (J : Finset ι) (bad : ι → Finset ℕ) (K : ℕ)
    (hbad : ∀ j ∈ J, (bad j).card ≤ K) :
    ∃ G ⊆ E, E.card ≤ G.card + J.card * K ∧
      ∀ a ∈ G, ∀ j ∈ J, a ∉ bad j := by
  let U := J.biUnion bad
  let G := E \ U
  have hU : U.card ≤ J.card * K := by
    calc
      _ ≤ ∑ j ∈ J, (bad j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ J, K := Finset.sum_le_sum hbad
      _ = _ := by simp
  refine ⟨G, Finset.sdiff_subset, ?_, ?_⟩
  · have hsplit := Finset.card_sdiff_add_card_inter E U
    have hinter : (E ∩ U).card ≤ U.card := Finset.card_le_card Finset.inter_subset_right
    dsimp [G]
    omega
  · intro a ha j hj hab
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_biUnion.mpr ⟨j, hj, hab⟩)

end Ostmann

end OAI
