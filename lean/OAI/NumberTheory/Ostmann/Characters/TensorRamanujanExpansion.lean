import OAI.NumberTheory.Ostmann.Supply.FiniteCoordinateEnergy

namespace OAI

/-! # Expansion of the reduced-frequency kernel by centered subset modes -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def centeredResidueGram {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (a b : ZMod p) : ℂ :=
  ∑ x, conj (centeredSupportProjection S (residuePointVector a) x) *
    centeredSupportProjection S (residuePointVector b) x

theorem tensorRamanujan_expansion {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (R : Finset (Fin n))
    (a b : ∀ i, ZMod (p i)) (ha : ∀ i ∈ R, a i ∈ S i) (hb : ∀ i ∈ R, b i ∈ S i) :
    (∏ i ∈ R, ∑ h ∈ Finset.univ.erase (0 : ZMod (p i)), ZMod.stdAddChar (h * (a i - b i))) =
      ∑ T ∈ R.powerset,
        (∏ i ∈ T, (p i : ℂ)) * (∏ i ∈ R \ T, ((p i : ℂ) / (S i).card - 1)) *
          ∏ i ∈ T, centeredResidueGram (S i) (a i) (b i) := by
  calc
    _ = ∏ i ∈ R, ((p i : ℂ) * centeredResidueGram (S i) (a i) (b i) +
        ((p i : ℂ) / (S i).card - 1)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [centeredRamanujanKernel (S i) (a i) (b i) (ha i hi) (hb i hi)]
      unfold centeredResidueGram
      ring
    _ = _ := by
      rw [Finset.prod_add]
      apply Finset.sum_congr rfl
      intro T _
      rw [Finset.prod_mul_distrib]
      ring

theorem tensorRamanujan_energy_expansion {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (R : Finset (Fin n)) {ι : Type*}
    (A : Finset ι) (a : ι → ∀ i, ZMod (p i)) (ha : ∀ x ∈ A, ∀ i ∈ R, a x i ∈ S i) :
    (A.card : ℂ)⁻¹ * (A.card : ℂ)⁻¹ * ∑ x ∈ A, ∑ y ∈ A,
      (∏ i ∈ R, ∑ h ∈ Finset.univ.erase (0 : ZMod (p i)), ZMod.stdAddChar (h * (a x i - a y i))) =
        ∑ T ∈ R.powerset, (∏ i ∈ T, (p i : ℂ)) *
          (∏ i ∈ R \ T, ((p i : ℂ) / (S i).card - 1)) *
            (centeredSubsetEnergy p S T A a : ℂ) := by
  have he (x) (hx : x ∈ A) (y) (hy : y ∈ A) :=
    tensorRamanujan_expansion p S R (a x) (a y) (ha x hx) (ha y hy)
  calc
    _ = (A.card : ℂ)⁻¹ * (A.card : ℂ)⁻¹ * ∑ x ∈ A, ∑ y ∈ A,
        ∑ T ∈ R.powerset, (∏ i ∈ T, (p i : ℂ)) *
          (∏ i ∈ R \ T, ((p i : ℂ) / (S i).card - 1)) *
            ∏ i ∈ T, centeredResidueGram (S i) (a x i) (a y i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_congr rfl (fun y hy => he x hx y hy)
    _ = _ := by
      simp_rw [Finset.sum_comm (s := A) (t := R.powerset)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      rw [centeredSubsetEnergy_formula]
      simp only [centeredResidueGram, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring

end Ostmann

end OAI
