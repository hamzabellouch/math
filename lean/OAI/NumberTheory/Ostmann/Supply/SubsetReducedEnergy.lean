import OAI.NumberTheory.Ostmann.Arithmetic.ReducedFrequencyEnergy

namespace OAI

/-! # Exact positive subset expansion of the classical reduced energy -/

namespace Ostmann
open scoped Classical BigOperators

theorem unitRamanujanKernel_subset {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (R : Finset (Fin n)) [NeZero (∏ i ∈ R, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) (z : ℤ) :
    unitRamanujanKernel (∏ i ∈ R, p i) (z : ZMod (∏ i ∈ R, p i)) =
      ∏ i ∈ R, ∑ h ∈ Finset.univ.erase (0 : ZMod (p i)),
        ZMod.stdAddChar (h * (z : ZMod (p i))) := by
  let : NeZero (∏ i : R, p i) := ⟨by
    rw [Finset.prod_coe_sort]
    exact NeZero.ne _⟩
  have hcR : Pairwise (fun i j : R => (p i).Coprime (p j)) := by
    intro i j hij
    exact hc (fun he => hij (Subtype.ext he))
  have hh := unitRamanujanKernel_product (fun i : R => p i) hcR z
  simp_rw [unitRamanujanKernel_prime] at hh
  have hq := Finset.prod_coe_sort R p
  have hr := Finset.prod_coe_sort R (fun i =>
    ∑ h ∈ Finset.univ.erase (0 : ZMod (p i)), ZMod.stdAddChar (h * (z : ZMod (p i))))
  rw [unitRamanujanKernel_int_congr hq z, hr] at hh
  exact hh

noncomputable def subsetSieveCoefficient {n : ℕ} (p : Fin n → ℕ)
    (S : ∀ i, Finset (ZMod (p i))) (R T : Finset (Fin n)) : ℝ :=
  (∏ i ∈ T, (p i : ℝ)) * (∏ i ∈ R \ T, ((p i : ℝ) / (S i).card - 1))

theorem subsetSieveCoefficient_nonneg {n : ℕ} (p : Fin n → ℕ)
    [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (R T : Finset (Fin n))
    (hS : ∀ i ∈ R, (S i).Nonempty) :
    0 ≤ subsetSieveCoefficient p S R T := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)
  · apply Finset.prod_nonneg
    intro i hi
    have hcard : (0 : ℝ) < (S i).card := by
      exact_mod_cast Finset.card_pos.mpr (hS i (Finset.mem_sdiff.mp hi).1)
    have hle : ((S i).card : ℝ) ≤ p i := by
      exact_mod_cast (Finset.card_le_univ (S i)).trans_eq (ZMod.card (p i))
    exact sub_nonneg.mpr ((le_div_iff₀ hcard).mpr (by simpa using hle))

theorem subset_reduced_energy_expansion {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] (S : ∀ i, Finset (ZMod (p i)))
    (R : Finset (Fin n)) [NeZero (∏ i ∈ R, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) {ι : Type*}
    (A : Finset ι) (a : ι → ℤ)
    (ha : ∀ x ∈ A, ∀ i ∈ R, (a x : ZMod (p i)) ∈ S i) :
    unitFrequencyEnergy A (fun x => (a x : ZMod (∏ i ∈ R, p i))) =
      ∑ T ∈ R.powerset, subsetSieveCoefficient p S R T *
        centeredSubsetEnergy p S T A (fun x i => (a x : ZMod (p i))) := by
  apply Complex.ofReal_injective
  rw [unitFrequencyEnergy_kernel]
  have hk (x y : ι) :
      unitRamanujanKernel (∏ i ∈ R, p i)
          ((a x : ZMod (∏ i ∈ R, p i)) - (a y : ZMod (∏ i ∈ R, p i))) =
        ∏ i ∈ R, ∑ h ∈ Finset.univ.erase (0 : ZMod (p i)),
          ZMod.stdAddChar (h * ((a x : ZMod (p i)) - (a y : ZMod (p i)))) := by
    simpa only [Int.cast_sub] using unitRamanujanKernel_subset p R hc (a x - a y)
  simp_rw [hk]
  rw [tensorRamanujan_energy_expansion p S R A (fun x i => (a x : ZMod (p i))) ha]
  simp only [subsetSieveCoefficient, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_one, mul_assoc]

end Ostmann

end OAI
