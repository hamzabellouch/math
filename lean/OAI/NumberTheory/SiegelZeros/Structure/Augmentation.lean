import Lean.Elab.Tactic.Omega
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.Basic
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.SelectedLengthContradiction

namespace OAI

namespace SiegelZeros

noncomputable section
namespace WeightedTorusJets.W25

open MvPolynomial

variable {σ K : Type*} [Fintype σ] [Field K]

omit [Fintype σ] in
theorem constantCoeff_ker_eq_idealOfVars :
    RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial σ K →+* K) =
      MvPolynomial.idealOfVars σ K := by
  ext p
  change p.coeff 0 = 0 ↔ p ∈ MvPolynomial.idealOfVars σ K
  rw [← pow_one (MvPolynomial.idealOfVars σ K), MvPolynomial.mem_pow_idealOfVars_iff']
  simp only [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff, forall_eq]

omit [Fintype σ] in
theorem truncationIdeal_le_constantCoeff_ker (t : σ → ℕ) :
    truncationIdeal (K := K) t ≤ RingHom.ker MvPolynomial.constantCoeff := by
  rw [truncationIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change MvPolynomial.constantCoeff ((X i : MvPolynomial σ K) ^ (t i + 1)) = 0
  simp

def augmentation (t : σ → ℕ) :
    (MvPolynomial σ K ⧸ truncationIdeal (K := K) t) →+* K :=
  Ideal.Quotient.lift (truncationIdeal (K := K) t) MvPolynomial.constantCoeff
    (truncationIdeal_le_constantCoeff_ker (K := K) t)

omit [Fintype σ] in
@[simp] theorem augmentation_mk (t : σ → ℕ) (p : MvPolynomial σ K) :
    augmentation (K := K) t (Ideal.Quotient.mk (truncationIdeal (K := K) t) p) = p.coeff 0 := rfl

omit [Fintype σ] in
theorem augmentation_surjective (t : σ → ℕ) :
    Function.Surjective (augmentation (K := K) t) := by
  intro c
  refine ⟨Ideal.Quotient.mk (truncationIdeal (K := K) t) (C c), ?_⟩
  simp

def augmentationIdeal (t : σ → ℕ) :
    Ideal (MvPolynomial σ K ⧸ truncationIdeal (K := K) t) := RingHom.ker (augmentation (K := K) t)

omit [Fintype σ] in
theorem augmentationIdeal_eq_map (t : σ → ℕ) :
    augmentationIdeal (K := K) t =
      (MvPolynomial.idealOfVars σ K).map (Ideal.Quotient.mk (truncationIdeal (K := K) t)) := by
  rw [augmentationIdeal, augmentation, Ideal.ker_quotient_lift,
    constantCoeff_ker_eq_idealOfVars]

theorem idealOfVars_pow_le_truncationIdeal (t : σ → ℕ) :
    MvPolynomial.idealOfVars σ K ^ ((∑ i, t i) + 1) ≤ truncationIdeal (K := K) t := by
  classical
  intro p hp
  rw [mem_truncationIdeal_iff]
  intro m hm
  have hdeg := (MvPolynomial.mem_pow_idealOfVars_iff _ p).mp hp m hm
  by_contra hn
  have hbound : ∀ i, m i ≤ t i := by
    simpa only [not_exists, not_le, Nat.lt_succ_iff] using hn
  have hsum : Finsupp.degree m ≤ ∑ i, t i := by
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum fun i _ => hbound i
  omega

theorem augmentationIdeal_pow_eq_bot (t : σ → ℕ) :
    augmentationIdeal (K := K) t ^ ((∑ i, t i) + 1) = ⊥ := by
  rw [augmentationIdeal_eq_map, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker,
    Ideal.mk_ker]
  exact idealOfVars_pow_le_truncationIdeal (K := K) t

instance augmentationIdeal_isMaximal (t : σ → ℕ) :
    (augmentationIdeal (K := K) t).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (augmentation_surjective (K := K) t)

theorem maximal_eq_augmentationIdeal (t : σ → ℕ)
    (M : Ideal (MvPolynomial σ K ⧸ truncationIdeal (K := K) t)) (hM : M.IsMaximal) :
    M = augmentationIdeal (K := K) t := by
  apply Eq.symm
  apply (augmentationIdeal_isMaximal (K := K) t).eq_of_le hM.ne_top
  intro x hx
  apply hM.isPrime.mem_of_pow_mem ((∑ i, t i) + 1)
  have hz : x ^ ((∑ i, t i) + 1) = 0 := by
    have hp := Ideal.pow_mem_pow hx ((∑ i, t i) + 1)
    rw [augmentationIdeal_pow_eq_bot] at hp
    exact hp
  rw [hz]
  exact M.zero_mem

instance truncatedQuotient_isLocalRing (t : σ → ℕ) :
    IsLocalRing (MvPolynomial σ K ⧸ truncationIdeal (K := K) t) := by
  apply IsLocalRing.of_unique_max_ideal
  exact ⟨augmentationIdeal (K := K) t, inferInstance, fun M hM => maximal_eq_augmentationIdeal (K := K) t M hM⟩

def augmentationResidueEquiv (t : σ → ℕ) :
    ((MvPolynomial σ K ⧸ truncationIdeal (K := K) t) ⧸ augmentationIdeal (K := K) t) ≃+* K :=
  (augmentation (K := K) t).quotientKerEquivOfSurjective (augmentation_surjective (K := K) t)

end WeightedTorusJets.W25

end

end SiegelZeros

end OAI
