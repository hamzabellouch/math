import OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals
import OAI.NumberTheory.PiExponent.Jets.TaylorRectangular

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryTaylor

open scoped BigOperators
open CommutingTaylor TaylorRectangular DerivativeIdeals
open PiExponentApprox

section General
variable {R K ι : Type*} [CommRing R] [Algebra ℚ R] [Field K] [Algebra ℚ K]

theorem wordDerivative_append (D : ι → Derivation ℚ R R)
    (u v : List ι) (a : R) :
    wordDerivative D (u ++ v) a = wordDerivative D u (wordDerivative D v a) := by
  induction u with
  | nil => rfl
  | cons i u ih => simp only [List.cons_append, wordDerivative_cons, ih]

theorem wordDerivative_replicate (D : ι → Derivation ℚ R R)
    (i : ι) (n : ℕ) (a : R) :
    wordDerivative D (List.replicate n i) a = iter (D i) n a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, wordDerivative_cons, ih, iter_succ]

theorem mixedIter_eq_wordDerivative (D : ι → Derivation ℚ R R)
    (k : ℕ) (B : Fin k → ι) (α : Fin k →₀ ℕ) (a : R) :
    mixedIter k (fun i => D (B i)) α a = wordDerivative D (derivativeWord k B α) a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [mixedIter, LinearMap.comp_apply, derivativeWord,
      wordDerivative_append, wordDerivative_replicate]
    exact ih (fun i => B i.succ) α.tail _

theorem derivativeWord_wordCost (k : ℕ) (B : Fin k → ι)
    (α : Fin k →₀ ℕ) (cost : ι → ℝ) :
    wordCost cost (derivativeWord k B α) = ∑ i, (α i : ℝ) * cost (B i) := by
  induction k with
  | zero => simp [derivativeWord, wordCost]
  | succ k ih =>
    simp only [derivativeWord, wordCost, List.map_append, List.sum_append,
      List.map_replicate, List.sum_replicate]
    change wordCost cost (derivativeWord k (fun i => B i.succ) α.tail) +
      (α 0) • cost (B 0) = _
    rw [ih, Fin.sum_univ_succ]
    simp only [Finsupp.tail_apply, nsmul_eq_mul]
    ring

theorem derivativeWord_wordCost_le (k : ℕ) (B : Fin k → ι)
    (α : Fin k →₀ ℕ) (cost : ι → ℝ) (n : Fin k → ℕ) (δ : ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (hα : ∀ i, α i < n i)
    (hn : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ) :
    wordCost cost (derivativeWord k B α) ≤ δ := by
  rw [derivativeWord_wordCost]
  apply le_trans _ hn
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_right _ (hcost _)
  exact_mod_cast (by have := hα i; omega : α i ≤ n i - 1)

theorem residueTaylor_ideal_le (D : ι → Derivation ℚ R R)
    (k : ℕ) (B : Fin k → ι) (ρ : R →+* K) (I : Ideal R)
    (cost : ι → ℝ) (n : Fin k → ℕ) (δ : ℝ)
    (hcost : ∀ i, 0 ≤ cost i)
    (hn : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ)
    (hvanish : ∀ a ∈ I, ∀ word : List ι, wordCost cost word ≤ δ →
      ρ (wordDerivative D word a) = 0) :
    I ≤ (TransverseMultiplicity.rectangularIdeal n).comap
      (residueTaylorFin k (fun i => D (B i)) ρ) := by
  intro a ha
  apply residueTaylor_mem_rectangular
  intro α hα
  rw [mixedIter_eq_wordDerivative]
  exact hvanish a ha _ (derivativeWord_wordCost_le k B α cost n δ hcost hα hn)

theorem persistent_ideal_le (D : ι → Derivation ℚ R R)
    (k : ℕ) (B : Fin k → ι) (ρ : R →+* K) (Q : Ideal R)
    (cost : ι → ℝ) (bound δ : ℝ) (F : R) (n : Fin k → ℕ)
    (hcost : ∀ i, 0 ≤ cost i)
    (hn : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ)
    (hpersist : derivativeIdeal D cost (bound + δ) F ≤ Q)
    (hQ : Q ≤ RingHom.ker ρ) :
    derivativeIdeal D cost bound F ≤ (TransverseMultiplicity.rectangularIdeal n).comap
      (residueTaylorFin k (fun i => D (B i)) ρ) := by
  apply residueTaylor_ideal_le D k B ρ _ cost n δ hcost hn
  intro a ha word hw
  exact hQ (derivative_vanishes_on_persistent_ideal D cost hcost bound δ F a Q ha hpersist word hw)

end General

variable {K : Type*} [Field K] [Algebra ℚ K]

def ordinaryTaylor (m k : ℕ) (B : Fin k → Fin m)
    (ρ : OrdinaryDerivatives.Polynomial m →+* K) :
    OrdinaryDerivatives.Polynomial m →+* MvPowerSeries (Fin k) K :=
  residueTaylorFin k (fun i => OrdinaryDerivatives.partialFrame m (B i)) ρ

omit [Algebra ℚ K] in
@[simp] theorem ordinaryTaylor_constant (m k : ℕ) (B : Fin k → Fin m)
    (ρ : OrdinaryDerivatives.Polynomial m →+* K) (a : OrdinaryDerivatives.Polynomial m) :
    MvPowerSeries.constantCoeff (ordinaryTaylor m k B ρ a) = ρ a :=
  constantCoeff_residueTaylorFin _ _ _ _

omit [Algebra ℚ K] in
@[simp] theorem ordinaryTaylor_firstCoefficient (m k : ℕ) (B : Fin k → Fin m)
    (ρ : OrdinaryDerivatives.Polynomial m →+* K) (i : Fin k)
    (a : OrdinaryDerivatives.Polynomial m) :
    MvPowerSeries.coeff (Finsupp.single i 1) (ordinaryTaylor m k B ρ a) =
      ρ (MvPolynomial.pderiv (B i) a) :=
  coeff_single_residueTaylorFin _ _ _ _ _

theorem mixedIter_eq_ordinaryWord (m k : ℕ) (B : Fin k → Fin m)
    (α : Fin k →₀ ℕ) (a : OrdinaryDerivatives.Polynomial m) :
    mixedIter k (fun i => OrdinaryDerivatives.partialFrame m (B i)) α a =
      OrdinaryDerivatives.word m (derivativeWord k B α) a :=
  mixedIter_eq_wordDerivative (OrdinaryDerivatives.partialFrame m) k B α a

theorem ordinaryTaylor_ideal_le (m k : ℕ) (B : Fin k → Fin m)
    (ρ : OrdinaryDerivatives.Polynomial m →+* K) (I : Ideal (OrdinaryDerivatives.Polynomial m))
    (cost : Fin m → ℝ) (n : Fin k → ℕ) (δ : ℝ)
    (hcost : ∀ i, 0 ≤ cost i)
    (hn : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ)
    (hvanish : ∀ a ∈ I, ∀ word : List (Fin m), wordCost cost word ≤ δ →
      ρ (OrdinaryDerivatives.word m word a) = 0) :
    I ≤ (TransverseMultiplicity.rectangularIdeal n).comap (ordinaryTaylor m k B ρ) :=
  residueTaylor_ideal_le (OrdinaryDerivatives.partialFrame m) k B ρ I cost n δ hcost hn hvanish

theorem ordinary_residueTaylor_ideal_le (m k : ℕ) (B : Fin k → Fin m)
    (ρ : OrdinaryDerivatives.Polynomial m →+* K) (I : Ideal (OrdinaryDerivatives.Polynomial m))
    (cost : Fin m → ℝ) (box : Fin k → ℕ) (δ : ℝ)
    (hcost : ∀ i, 0 ≤ cost i)
    (hbudget : ∑ i, ((box i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ)
    (hvanish : ∀ a ∈ I, ∀ word : List (Fin m), wordCost cost word ≤ δ →
      ρ (OrdinaryDerivatives.word m word a) = 0) :
    I ≤ (TransverseMultiplicity.rectangularIdeal box).comap
      (residueTaylorFin k (fun i => OrdinaryDerivatives.partialFrame m (B i)) ρ) :=
  ordinaryTaylor_ideal_le m k B ρ I cost box δ hcost hbudget hvanish

theorem ordinary_persistent_ideal_le (m k : ℕ) (B : Fin k → Fin m)
    (ρ : OrdinaryDerivatives.Polynomial m →+* K) (Q : Ideal (OrdinaryDerivatives.Polynomial m))
    (cost : Fin m → ℝ) (bound δ : ℝ) (F : OrdinaryDerivatives.Polynomial m)
    (n : Fin k → ℕ) (hcost : ∀ i, 0 ≤ cost i)
    (hn : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ)
    (hpersist : OrdinaryDerivatives.ideal m cost (bound + δ) F ≤ Q)
    (hQ : Q ≤ RingHom.ker ρ) :
    OrdinaryDerivatives.ideal m cost bound F ≤
      (TransverseMultiplicity.rectangularIdeal n).comap (ordinaryTaylor m k B ρ) :=
  persistent_ideal_le (OrdinaryDerivatives.partialFrame m) k B ρ Q cost bound δ F n
    hcost hn hpersist hQ

end PiExponent.OrdinaryTaylor
end

end OAI
