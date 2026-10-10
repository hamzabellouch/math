import OAI.NumberTheory.Ostmann.Supply.IndexedMultiplierWeights

namespace OAI

/-! # Integer multipliers supply the actual subset extension weights -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def primeProductSubsets {n : ℕ} (p : Fin n → ℕ) (Q : ℕ) :
    Finset (Finset (Fin n)) := Finset.univ.filter (fun R => (∏ i ∈ R, p i) ≤ Q)

theorem concrete_extension_weight_lower {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (κ : ℕ → ℝ) (hκ : ∀ q ∈ Finset.univ.image p, 0 < κ q)
    (hκS : ∀ i, κ (p i) = (p i : ℝ) / (S i).card - 1)
    (Q : ℕ) (T : Finset (Fin n))
    (hcover : ∀ q, Nat.Prime q → q ≤ Q → ∃ i, p i = q)
    (B : ℝ) (hB : 0 < B)
    (hT : (∑ q ∈ T.image p, (q : ℝ)⁻¹) ≤ 1 / 16)
    (hP : (∑ q ∈ Finset.univ.image p, |Real.log (κ q)| / q) ≤ B / 16) :
    ((∏ i ∈ T, p i : ℕ) : ℝ) * ((Q / (∏ i ∈ T, p i) : ℕ) : ℝ) / 8 * Real.exp (-B) ≤
      ∑ R ∈ primeProductSubsets p Q,
        if T ⊆ R then subsetSieveCoefficient p S R T else 0 := by
  let t := ∏ i ∈ T, p i
  let U := Q / t
  let P := Finset.univ.image p
  let D := (positiveMultipliers U).filter (fun u => Squarefree u ∧ u.Coprime t)
  have hTprod : (∏ q ∈ T.image p, q) = t := by
    rw [Finset.prod_image]
    exact fun _ _ _ _ h => coprime_prime_family_injective p hc h
  have hTprime : ∀ q ∈ T.image p, Nat.Prime q := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact Fact.out
  have hweighted := weighted_multiplier_supply U (T.image p) P κ hκ hTprime B hB hT hP
  rw [hTprod] at hweighted
  change (U : ℝ) / 8 * Real.exp (-B) ≤ ∑ u ∈ D, multiplierRatioProduct P κ u at hweighted
  have hsq (u) (hu : u ∈ D) : Squarefree u := (Finset.mem_filter.mp hu).2.1
  have hcop (u) (hu : u ∈ D) : u.Coprime t := (Finset.mem_filter.mp hu).2.2
  have hcov (u) (hu : u ∈ D) (q) (hq : q ∈ u.primeFactors) : ∃ i, p i = q := by
    apply hcover q (Nat.mem_primeFactors.mp hq).1
    have hqu : q ≤ u := Nat.le_of_dvd (Nat.pos_of_ne_zero (hsq u hu).ne_zero)
      (Nat.mem_primeFactors.mp hq).2.1
    have huU : u ≤ U := (Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1).2
    exact hqu.trans (huU.trans (Nat.div_le_self Q t))
  have hinj := primeIndexExtension_injective p hc T D hsq hcov hcop
  have himage : D.image (fun u => T ∪ primeDivisorIndices p u) ⊆ primeProductSubsets p Q := by
    intro R hR
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hR
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [primeIndexExtension_product p hc T (hsq u hu) (hcov u hu) (hcop u hu)]
    have huU : u ≤ U := (Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1).2
    exact (Nat.mul_le_mul_left t huU).trans (by simpa [Nat.mul_comm] using Nat.div_mul_le_self Q t)
  calc
    _ = (t : ℝ) * ((U : ℝ) / 8 * Real.exp (-B)) := by dsimp [t, U]; ring
    _ ≤ (t : ℝ) * ∑ u ∈ D, multiplierRatioProduct P κ u :=
      mul_le_mul_of_nonneg_left hweighted (Nat.cast_nonneg t)
    _ = ∑ R ∈ D.image (fun u => T ∪ primeDivisorIndices p u),
        if T ⊆ R then subsetSieveCoefficient p S R T else 0 := by
      rw [Finset.sum_image hinj]
      simp only [Finset.subset_union_left, ite_true]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [primeIndexExtension_coefficient p hc S κ hκS T (hcop u hu), Nat.cast_prod]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro R _ _
      split_ifs
      · exact subsetSieveCoefficient_nonneg p S R T (fun i _ => hS i)
      · exact le_rfl

end Ostmann

end OAI
