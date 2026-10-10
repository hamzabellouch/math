import OAI.Geometry.NodalSets.Waves.FiniteWaveJet

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

lemma homogeneousComponent_pderiv (p : CPoly) (n : ℕ) (i : Fin 4) :
    homogeneousComponent n (pderiv i p) = pderiv i (homogeneousComponent (n + 1) p) := by
  ext d
  simp only [coeff_homogeneousComponent, coeff_pderiv, map_add, Finsupp.degree_single]
  by_cases hd : d.degree = n
  · simp [hd]
  · simp [hd]

theorem homogeneousComponent_mul (p q : CPoly) (n : ℕ) :
    homogeneousComponent n (p * q) = ∑ r ∈ Finset.range (n + 1),
      homogeneousComponent r p * homogeneousComponent (n - r) q := by
  let A := homogeneousSubmodule (Fin 4) ℂ
  have hd (p : CPoly) (k : ℕ) :
      ((DirectSum.decompose A p) k : CPoly) = homogeneousComponent k p :=
    MvPolynomial.decomposition.decompose'_apply p k
  rw [← hd, DirectSum.decompose_mul, DirectSum.coe_mul_apply_eq_sum_antidiagonal]
  simp only [hd]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j ↦ homogeneousComponent i p * homogeneousComponent j q) n

def polynomialSecondOrder (g : Fin 4 → Fin 4 → CPoly) (b : Fin 4 → CPoly) (p : CPoly) : CPoly :=
  (∑ i, ∑ j, g i j * pderiv i (pderiv j p)) + ∑ i, b i * pderiv i p

theorem secondOrderCoefficient_eq (g : Fin 4 → Fin 4 → CPoly) (b : Fin 4 → CPoly)
    (p : CPoly) (n : ℕ) :
    secondOrderCoefficient (fun r i j ↦ homogeneousComponent r (g i j))
      (fun r i ↦ homogeneousComponent r (b i)) (polynomialJet p) n =
      homogeneousComponent n (polynomialSecondOrder g b p) := by
  unfold secondOrderCoefficient polynomialSecondOrder polynomialJet
  have he : ((∑ r ∈ Finset.range (n + 1), ∑ i, ∑ j,
      homogeneousComponent r (g i j) * pderiv i (pderiv j (homogeneousComponent (n - r + 2) p))) +
      ∑ r ∈ Finset.range (n + 1), ∑ i,
        homogeneousComponent r (b i) * pderiv i (homogeneousComponent (n - r + 1) p)) =
      homogeneousComponent n ((∑ i, ∑ j, g i j * pderiv i (pderiv j p)) +
        ∑ i, b i * pderiv i p) := by
    simp only [map_add, map_sum, homogeneousComponent_mul, homogeneousComponent_pderiv]
    apply congrArg₂ (· + ·)
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    · rw [Finset.sum_comm]
  rw [he, homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous _ _)]

def polynomialTransport (W : Fin 4 → CPoly) (c f a : CPoly) : CPoly :=
  (∑ i, W i * pderiv i a) + c * a - f

theorem transportCoefficient_eq (w : Fin 4 → ℂ) (W : Fin 4 → CPoly)
    (hW : ∀ i, homogeneousComponent 0 (W i) = C (w i)) (c f a : CPoly) (n : ℕ) :
    transportCoefficient w (fun r i ↦ homogeneousComponent r (W i))
      (polynomialJet c) (polynomialJet f) n (polynomialJet a) =
      homogeneousComponent n (polynomialTransport W c f a) := by
  unfold transportCoefficient polynomialTransport polynomialJet
  have hw (r : ℕ) (i : Fin 4) :
      (if r = 0 then C (w i) else homogeneousComponent r (W i)) =
        homogeneousComponent r (W i) := by
    split_ifs with h
    · subst r; exact (hW i).symm
    · rfl
  simp only [hw]
  have he : ((∑ r ∈ Finset.range (n + 1), ∑ i,
      homogeneousComponent r (W i) * pderiv i (homogeneousComponent (n - r + 1) a)) +
      (∑ r ∈ Finset.range (n + 1), homogeneousComponent r c * homogeneousComponent (n - r) a) -
      homogeneousComponent n f) =
      homogeneousComponent n ((∑ i, W i * pderiv i a) + c * a - f) := by
    simp only [map_sub, map_add, map_sum, homogeneousComponent_mul, homogeneousComponent_pderiv]
    rw [Finset.sum_comm]
  rw [he, homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous _ _)]

end
end Yau.Jets

end OAI
