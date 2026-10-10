import OAI.Analysis.MutuallyUnbiased.PairMoments.PairPermutations

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def FourierZero (H : CMatrix) : Prop :=
  ∀ π : Equiv.Perm Coord, g (fun i j => H (π i) j) alpha = 0

def PairProductsZero (H : CMatrix) : Prop :=
  ∀ π : Equiv.Perm Coord,
    g (fun i j => H (π i) j) alpha * g (fun i j => H (π i) j) qCross = 0 ∧
    g (fun i j => H (π i) j) alpha * g (fun i j => H (π i) j) qSame = 0

theorem doubleDifference_zero_of_pair_products {H : CMatrix} (hH : IsHadamard H)
    (hp : PairProductsZero H) (ha : g H alpha ≠ 0) (i j : Coord) (hij : i ≠ j) :
    g H (doubleDifference i j) = 0 := by
  obtain ⟨π, hπα, hπq⟩ := pair_permutation_witness i j hij
  have hn : g (fun i j => H (π i) j) alpha ≠ 0 := by
    rw [g_row_permutation]
    rcases hπα with h | h
    · rw [h]
      exact ha
    · rw [h, g_neg hH]
      exact fun hzero => ha ((map_eq_zero (starRingEnd ℂ)).mp hzero)
  rcases hπq with h | h
  · have hz := (mul_eq_zero.mp (hp π).1).resolve_left hn
    rwa [g_row_permutation, h] at hz
  · have hz := (mul_eq_zero.mp (hp π).2).resolve_left hn
    rwa [g_row_permutation, h] at hz

theorem pair_products_row_permutation {H : CMatrix} (hp : PairProductsZero H)
    (π : Equiv.Perm Coord) : PairProductsZero (fun i j => H (π i) j) := by
  intro σ
  exact hp (σ.trans π)

/-- The manuscript's single-matrix dichotomy, conditional here only on the two
explicit pair-product identities. The finite certificate supplies them. -/
theorem dichotomy_of_pair_products {H : CMatrix} (hH : IsHadamard H)
    (hp : PairProductsZero H) : FourierZero H ∨ IsHadamard (fun i j => H i j ^ 2) := by
  classical
  by_cases hzero : FourierZero H
  · exact Or.inl hzero
  · right
    obtain ⟨π, hπ⟩ := not_forall.mp hzero
    let K : CMatrix := fun i j => H (π i) j
    have hK : IsHadamard K := hH.permutations π (Equiv.refl _)
    have hKp : PairProductsZero K := pair_products_row_permutation hp π
    have hKsquare : IsHadamard (fun i j => K i j ^ 2) :=
      square_isHadamard_of_doubleDifference_zero hK
        (doubleDifference_zero_of_pair_products hK hKp hπ)
    have h := hKsquare.permutations π.symm (Equiv.refl _)
    simpa only [K, Equiv.apply_symm_apply, Equiv.refl_apply] using h

theorem dichotomy_of_pair_certificates {H : CMatrix} (hH : IsHadamard H)
    (hcross : PairCertificateIdentity H qCross) (hsame : PairCertificateIdentity H qSame) :
    FourierZero H ∨ IsHadamard (fun i j => H i j ^ 2) := by
  apply dichotomy_of_pair_products hH
  intro π
  exact ⟨pair_product_zero_of_certificate hcross π, pair_product_zero_of_certificate hsame π⟩

end MUB6

end

end OAI
