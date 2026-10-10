import OAI.NumberTheory.PiExponent.Geometry.FiniteNormalizationGrowth
import OAI.NumberTheory.PiExponent.LocalAlgebra.CumulativeHilbertSections
import OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertGrowthComparison
import OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertPolynomial
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialCumulative
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks

namespace OAI

namespace PiExponentJets.W24

open MvPolynomial Polynomial Finset
open PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem normalization_binomial_lower_bound (s : ℕ)
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial (Fin s) k →ₐ[k] (MvPolynomial σ k ⧸ I))
    (hg : Function.Injective g) (F : Fin s → MvPolynomial σ k)
    (hF : ∀ i, Ideal.Quotient.mk I (F i) = g (MvPolynomial.X i))
    (D : ℕ) (hD : ∀ i, (F i).totalDegree ≤ D) (m : ℕ) :
    (m + s).choose s ≤ Module.finrank k (quotientDegreeFiltration I (D * m)) := by
  let L : restrictTotalDegree (Fin s) k m →ₗ[k]
      quotientDegreeFiltration I (D * m) :=
    { toFun := fun p => ⟨g p, by
        simpa only [Nat.mul_comm D m] using
          normalization_mem_quotientDegreeFiltration I g F hF D hD m p
            ((mem_restrictTotalDegree _ _ _).mp p.property)⟩
      map_add' := fun p q => Subtype.ext (g.map_add p q)
      map_smul' := fun c p => Subtype.ext (g.toLinearMap.map_smul c p) }
  rw [← W32.finrank_restrictTotalDegree k s m]
  exact LinearMap.finrank_le_finrank_of_injective (f := L)
    (fun p q h => Subtype.ext (hg (congrArg Subtype.val h)))

theorem normalization_binomial_lower_growth (s : ℕ)
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial (Fin s) k →ₐ[k] (MvPolynomial σ k ⧸ I))
    (hg : Function.Injective g) :
    ∃ D : ℕ, 0 < D ∧ ∀ m : ℕ,
      (m + s).choose s ≤ Module.finrank k (quotientDegreeFiltration I (D * m)) := by
  classical
  choose F hF using fun i : Fin s => Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let D := max (Finset.univ.sup fun i => (F i).totalDegree) 1
  have hD : ∀ i, (F i).totalDegree ≤ D := fun i =>
    (Finset.le_sup (f := fun j : Fin s => (F j).totalDegree)
      (Finset.mem_univ i)).trans (le_max_left _ _)
  exact ⟨D, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _),
    normalization_binomial_lower_bound s I g hg F hF D hD⟩

theorem prime_quotientDegreeFiltration_finrank_pos
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule σ k))
    (i : σ) (hi : MvPolynomial.X i ∉ P) (n : ℕ) :
    0 < Module.finrank k (quotientDegreeFiltration P n) := by
  rw [W25.quotientDegreeFiltration_finrank_eq_sum P hP n]
  exact (W27.prime_quotientSection_finrank_pos P i hi 0).trans_le
    (Finset.single_le_sum (s := Finset.range (n + 1)) (a := 0)
      (f := fun j => Module.finrank k (quotientSection P j))
      (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.zero_lt_succ n)))

theorem prime_hilbert_natDegree_add_one_eq_krullDim
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule σ k))
    (i : σ) (hi : MvPolynomial.X i ∉ P)
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) =
      (Module.finrank k (quotientSection P n) : ℚ)) :
    (p.natDegree + 1 : WithBot ℕ∞) = ringKrullDim (MvPolynomial σ k ⧸ P) := by
  have hpl : 0 < p.leadingCoeff :=
    W27.polynomial_leadingCoeff_pos_of_eventually_pos p N (by
      intro n hn
      rw [hp n hn]
      exact_mod_cast W27.prime_quotientSection_finrank_pos P i hi n)
  have hp0 : p ≠ 0 := leadingCoeff_ne_zero.mp (ne_of_gt hpl)
  obtain ⟨q, hqd, hq⟩ := exists_eventual_cumulative_polynomial
    (fun n => Module.finrank k (quotientSection P n)) p hp0 N hp
  have hqv (n : ℕ) (hn : N ≤ n) :
      q.eval (n : ℚ) = (Module.finrank k (quotientDegreeFiltration P n) : ℚ) := by
    rw [hq n hn, W25.quotientDegreeFiltration_finrank_eq_sum P hP n]
  have hql : 0 < q.leadingCoeff :=
    W27.polynomial_leadingCoeff_pos_of_eventually_pos q N (by
      intro n hn
      rw [hqv n hn]
      exact_mod_cast prime_quotientDegreeFiltration_finrank_pos P hP i hi n)
  obtain ⟨s, g, hg, hfin, hdim⟩ :=
    exists_finite_normalization_with_dimension k (MvPolynomial σ k ⧸ P)
  obtain ⟨D, hD, hlo⟩ := normalization_binomial_lower_growth s P g hg
  obtain ⟨C, E, hC, hup⟩ := W29.finite_normalization_upper_growth P g hfin
  have hdeg : q.natDegree = s := natDegree_eq_of_polynomial_growth_bounds
      q (W32.polynomialGrowth s) (W32.scaledPolynomialGrowth C s) s
      hql (W32.polynomialGrowth_leadingCoeff_pos s)
      (W32.polynomialGrowth_natDegree s) (W32.scaledPolynomialGrowth_natDegree_le C s)
      (D : ℚ) 0 (C : ℚ) (E : ℚ) N (by
        intro n hn
        have hDn : N ≤ D * n := hn.trans (by nlinarith)
        rw [add_zero, ← Nat.cast_mul, hqv (D * n) hDn, W32.polynomialGrowth_eval]
        exact_mod_cast hlo n) (by
        intro n hn
        rw [hqv n hn, ← Nat.cast_mul, ← Nat.cast_add,
          W32.scaledPolynomialGrowth_eval_finrank k C s (C * n + E)]
        exact_mod_cast hup n)
  rw [hdim, ← hdeg, hqd]
  norm_cast

theorem exists_prime_hilbert_polynomial_with_dimension
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule σ k))
    (i : σ) (hi : MvPolynomial.X i ∉ P) :
    ∃ p : Polynomial ℚ,
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) =
        (Module.finrank k (quotientSection P n) : ℚ)) ∧
      (p.natDegree + 1 : WithBot ℕ∞) = ringKrullDim (MvPolynomial σ k ⧸ P) := by
  obtain ⟨p, N, hp⟩ := exists_homogeneous_hilbert_polynomial σ P hP
  have hp' (n : ℕ) (hn : N + 1 ≤ n) := (hp n (by omega)).symm
  exact ⟨p, ⟨N + 1, hp'⟩,
    prime_hilbert_natDegree_add_one_eq_krullDim P hP i hi p (N + 1) hp'⟩

end PiExponentJets.W24

end OAI
