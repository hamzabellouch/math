import Mathlib
import OAI.Probability.BinarySweep.TensorBounds.SignedCommutant
import OAI.Probability.BinarySweep.MatrixBounds.MatrixProjection
import OAI.Probability.BinarySweep.TensorBounds.SignedPinching

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder
open Equiv Equiv.Perm Matrix Representation

namespace BinaryCoordinateSweeps.Signed
open Density Irrep

variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}

omit [DecidableEq A] in
lemma coeff_actHilbert (p : A → Bool) (g : Equiv.Perm (Fin n)) (v : TensorSpace A n) :
    coeffEquiv A n (actHilbert p g v) = act p g (coeffEquiv A n v) := rfl

omit [DecidableEq A] in
lemma coeff_symm_act (p : A → Bool) (g : Equiv.Perm (Fin n)) (v : (Fin n → A) → ℂ) :
    (coeffEquiv A n).symm (act p g v) = actHilbert p g ((coeffEquiv A n).symm v) := rfl

def projectionIntertwiner (p : A → Bool) (S : Submodule ℂ ((Fin n → A) → ℂ))
    (hS : ∀ g, S.map (act p g) = S) :
    IntertwiningMap (tensorRep p n) (tensorRep p n) where
  toLinearMap := (coeffEquiv A n).conj (hilbertSubspace S).starProjection.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change coeffEquiv A n ((hilbertSubspace S).starProjection ((coeffEquiv A n).symm (act p g v))) =
      act p g (coeffEquiv A n ((hilbertSubspace S).starProjection ((coeffEquiv A n).symm v)))
    rw [coeff_symm_act, ← coeff_actHilbert]
    congr 1
    exact (projectionMatrix_commutes (hilbertSubspace S) (actionIsometry p g)
      (hilbertSubspace_map p S hS g) ((coeffEquiv A n).symm v)).symm

lemma projectionMatrix_invariant (p : A → Bool) (S : Submodule ℂ ((Fin n → A) → ℂ))
    (hS : ∀ g, S.map (act p g) = S) :
    Invariant p (projectionMatrix (hilbertSubspace S)) := by
  have h := intertwiner_matrix_invariant p (projectionIntertwiner p S hS)
  change Invariant p (LinearMap.toMatrix' ((coeffEquiv A n).conj
    (hilbertSubspace S).starProjection.toLinearMap)) at h
  rw [show coeffEquiv A n = WithLp.linearEquiv 2 ℂ ((Fin n → A) → ℂ) from rfl,
    projectionMatrix_coeff] at h
  exact h

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def isotypicProjection (p : A → Bool) (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    Matrix (Fin n → A) (Fin n → A) ℂ :=
  projectionMatrix (hilbertSubspace (isotypicSpan ρ (tensorRep p n)))

omit [FiniteDimensional ℂ V] in
lemma isotypicProjection_psd (p : A → Bool) (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    (isotypicProjection p ρ).PosSemidef := projectionMatrix_psd _

omit [FiniteDimensional ℂ V] in
lemma isotypicProjection_invariant (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) : Invariant p (isotypicProjection p ρ) := by
  apply projectionMatrix_invariant
  exact isotypicSpan_map ρ (tensorRep p n)

omit [FiniteDimensional ℂ V] in
lemma isotypicProjection_trace (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    (isotypicProjection p ρ).trace =
      (Module.finrank ℂ (isotypicSpan ρ (tensorRep p n)) : ℂ) := by
  rw [isotypicProjection, projectionMatrix_trace, hilbertSubspace_finrank]

lemma isotypicSpan_rank_bound (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible] :
    Module.finrank ℂ (isotypicSpan ρ (tensorRep p n)) ≤
      Module.finrank ℂ V * (n+1)^((Fintype.card A)^2) := by
  exact (isotypicSpan_finrank ρ (tensorRep p n)).trans (Nat.mul_le_mul_left _
    ((multiplicity_le_commutant ρ (tensorRep p n)).trans (tensor_commutant_finrank p n)))

theorem isotypic_density_domination (n : ℕ) (hn : 0 < n) (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible] :
    (((Module.finrank ℂ V : ℂ) * (n+1 : ℂ)^(2*(Fintype.card A)^2)) •
      (∑ c : WordType (MatchedPair p) n, ∑ t : MatchedPair p → ZMod (n+1),
        matrixTensorPower n (reducedPhaseDensity n (matchedEmbedding p) c t)) -
      isotypicProjection p ρ).PosSemidef := by
  let Q := ∑ c : WordType (MatchedPair p) n, ∑ t : MatchedPair p → ZMod (n+1),
        matrixTensorPower n (reducedPhaseDensity n (matchedEmbedding p) c t)
  have hQ : Q.PosSemidef := by
    apply Matrix.posSemidef_sum
    intro c _
    apply Matrix.posSemidef_sum
    intro t _
    rw [reducedPhaseDensity, ← tensor_gram]
    exact gram_psd _
  have hd := signed_psd_postselection n hn p (isotypicProjection p ρ)
    (isotypicProjection_psd p ρ) (isotypicProjection_invariant p ρ)
  rw [isotypicProjection_trace] at hd
  simp only [Nat.cast_add, Nat.cast_one] at hd
  have hr : (Module.finrank ℂ (isotypicSpan ρ (tensorRep p n)) : ℂ) ≤
      (Module.finrank ℂ V : ℂ) * (n+1 : ℂ)^((Fintype.card A)^2) := by
    exact_mod_cast isotypicSpan_rank_bound p ρ
  have hc : (0 : ℂ) ≤ (n+1 : ℂ)^((Fintype.card A)^2) := by positivity
  have hh := hQ.smul (mul_nonneg hc (sub_nonneg.mpr hr))
  have he : (n+1 : ℂ)^((Fintype.card A)^2) *
        ((Module.finrank ℂ V : ℂ) * (n+1 : ℂ)^((Fintype.card A)^2) -
          (Module.finrank ℂ (isotypicSpan ρ (tensorRep p n)) : ℂ)) +
        (n+1 : ℂ)^((Fintype.card A)^2) *
          (Module.finrank ℂ (isotypicSpan ρ (tensorRep p n)) : ℂ) =
      (Module.finrank ℂ V : ℂ) * (n+1 : ℂ)^(2*(Fintype.card A)^2) := by
    rw [two_mul, pow_add]
    ring
  have hi := hh.add hd
  change (_ • Q + (_ • Q - isotypicProjection p ρ)).PosSemidef at hi
  rw [← add_sub_assoc, ← add_smul, he] at hi
  exact hi

end BinaryCoordinateSweeps.Signed

end

end OAI
