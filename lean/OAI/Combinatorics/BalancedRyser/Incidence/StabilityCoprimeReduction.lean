import Mathlib.RingTheory.EuclideanDomain
import OAI.Combinatorics.BalancedRyser.Incidence.StabilityLeadingPart

namespace OAI

namespace Balanced.StabilityCoprimeReduction

open Polynomial
open StabilityPolynomial
open scoped BigOperators

variable {F : Type*} [Field F]

theorem exists_coprime_grid_reduction
    (H f g : F[X]) (q : ℕ) (hH : H ≠ 0) (hf : f ≠ 0)
    (heq : H = X ^ q * f + g) :
    ∃ D f₀ g₀ : F[X],
      D ≠ 0 ∧ IsCoprime f₀ g₀ ∧ f₀ ≠ 0 ∧
      f₀.natDegree ≤ f.natDegree ∧ g₀.natDegree ≤ g.natDegree ∧
      f = D * f₀ ∧ g = D * g₀ ∧
      H = D * (X ^ q * f₀ + g₀) ∧
      X ^ q * f₀ + g₀ ≠ 0 ∧ X ^ q * f₀ + g₀ ∣ H := by
  classical
  let : GCDMonoid F[X] := EuclideanDomain.gcdMonoid F[X]
  let D := GCDMonoid.gcd f g
  have hD : D ≠ 0 := gcd_ne_zero_of_left hf
  have hDf : D * (f / D) = f :=
    EuclideanDomain.mul_div_cancel' hD (GCDMonoid.gcd_dvd_left f g)
  have hDg : D * (g / D) = g :=
    EuclideanDomain.mul_div_cancel' hD (GCDMonoid.gcd_dvd_right f g)
  have hfactor : H = D * (X ^ q * (f / D) + g / D) := by
    calc
      H = X ^ q * f + g := heq
      _ = X ^ q * (D * (f / D)) + D * (g / D) := by rw [hDf, hDg]
      _ = D * (X ^ q * (f / D) + g / D) := by ring
  have hquot : X ^ q * (f / D) + g / D ≠ 0 := by
    intro hz
    apply hH
    simpa [hz] using hfactor
  refine ⟨D, f / D, g / D, hD,
    isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hD,
    left_div_gcd_ne_zero hf,
    natDegree_le_natDegree (degree_div_le f D),
    natDegree_le_natDegree (degree_div_le g D),
    hDf.symm, hDg.symm, hfactor, hquot, ?_⟩
  exact ⟨D, hfactor.trans (mul_comm _ _)⟩

theorem redeiLeadingProduct_monic (U : Finset (Point F)) :
    (redeiLeadingProduct U).Monic :=
  monic_prod_of_monic U (fun p : Point F => X + C p.1)
    (fun p _ => monic_X_add_C p.1)

theorem redeiLeadingProduct_natDegree (U : Finset (Point F)) :
    (redeiLeadingProduct U).natDegree = U.card := by
  classical
  rw [redeiLeadingProduct, natDegree_prod_of_monic U
    (fun p : Point F => X + C p.1) (fun p _ => monic_X_add_C p.1)]
  simp

theorem multiplier_ne_zero_of_low_remainder
    (R A f g : F[X]) (q : ℕ) (hR : R ≠ 0) (hA : A ≠ 0)
    (hg : g.natDegree < R.natDegree)
    (heq : R * A = X ^ q * f + g) : f ≠ 0 := by
  intro hf
  have hRA : R * A = g := by simpa [hf] using heq
  have hdeg := congrArg Polynomial.natDegree hRA
  rw [natDegree_mul hR hA] at hdeg
  omega

variable [Fintype F]

theorem card_le_card_add_auxiliary_bound
    (U : Finset (Point F)) (d : ℕ)
    (hsize : 2 * (nonverticalSkewCodes U).card < (d + 1) * (d + 2)) :
    Fintype.card F ≤ U.card + d := by
  obtain ⟨a, ha, had, hvan⟩ := exists_redei_auxiliary U d hsize
  exact (card_le_redei_auxiliary_degree U a ha hvan).trans (Nat.add_le_add_left had U.card)

theorem exists_coprime_redei_identity
    (U : Finset (Point F)) (d : ℕ)
    (hsize : 2 * (nonverticalSkewCodes U).card < (d + 1) * (d + 2))
    (hdq : d < Fintype.card F) :
    ∃ A D f g : F[X],
      A ≠ 0 ∧ A.natDegree ≤ d ∧ D ≠ 0 ∧ IsCoprime f g ∧ f ≠ 0 ∧
      f.natDegree ≤ U.card + d - Fintype.card F ∧
      g.natDegree ≤ U.card + d - Fintype.card F ∧
      redeiLeadingProduct U * A = D * (X ^ Fintype.card F * f + g) ∧
      X ^ Fintype.card F * f + g ≠ 0 ∧
      X ^ Fintype.card F * f + g ∣ redeiLeadingProduct U * A := by
  obtain ⟨A, f, g, hA, hAd, hfdeg, hgdeg, heq⟩ := exists_redei_leading_identity U d hsize
  have hR : redeiLeadingProduct U ≠ 0 := (redeiLeadingProduct_monic U).ne_zero
  have horder := card_le_card_add_auxiliary_bound U d hsize
  have hU : 0 < U.card := by omega
  have hsmall : g.natDegree < (redeiLeadingProduct U).natDegree := by
    rw [redeiLeadingProduct_natDegree]
    omega
  have hf : f ≠ 0 := multiplier_ne_zero_of_low_remainder _ _ _ _ _ hR hA hsmall heq
  obtain ⟨D, f₀, g₀, hD, hcop, hf₀, hfd, hgd, _, _, hfactor, hnonzero, hdiv⟩ :=
    exists_coprime_grid_reduction (redeiLeadingProduct U * A) f g (Fintype.card F)
      (mul_ne_zero hR hA) hf heq
  exact ⟨A, D, f₀, g₀, hA, hAd, hD, hcop, hf₀,
    hfd.trans hfdeg, hgd.trans hgdeg, hfactor, hnonzero, hdiv⟩

end Balanced.StabilityCoprimeReduction

end OAI
