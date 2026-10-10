import Mathlib
import OAI.Probability.BinarySweep.TensorBounds.BlockTypes

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {I A : Type*} [Fintype I] [LinearOrder I]
  [Fintype A] [DecidableEq A] {n : I → ℕ} {N : ℕ}
  {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

def groupOf (e : (Σₗ i, Fin (n i)) ≃o Fin N) (g : Equiv.Perm (Fin N)) (t : Fin N) : I :=
  (ofLex (e.symm (g⁻¹ t))).1

def groupedProjection (e : (Σₗ i, Fin (n i)) ≃o Fin N) (g : Equiv.Perm (Fin N))
    (p : A → Bool) (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) :=
  signedConj p g (blockProjection e p ρ)

omit [∀i, FiniteDimensional ℂ (V i)] in
lemma groupedProjection_psd (e : (Σₗ i, Fin (n i)) ≃o Fin N) (g : Equiv.Perm (Fin N))
    (p : A → Bool) (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) :
    (groupedProjection e g p ρ).PosSemidef :=
  signedConj_psd p g _ (blockProjection_psd e p ρ)

omit [∀i, FiniteDimensional ℂ (V i)] in
lemma groupedProjection_idempotent (e : (Σₗ i, Fin (n i)) ≃o Fin N) (g : Equiv.Perm (Fin N))
    (p : A → Bool) (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) :
    groupedProjection e g p ρ*groupedProjection e g p ρ=groupedProjection e g p ρ := by
  unfold groupedProjection
  rw [← signedConj_mul,blockProjection_idempotent]

omit [∀i, FiniteDimensional ℂ (V i)] in
lemma groupedProjection_commutes (e : (Σₗ i, Fin (n i)) ≃o Fin N) (g : Equiv.Perm (Fin N))
    (p : A → Bool) (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    (M : Matrix (Fin N → A) (Fin N → A) ℂ) (hM : Invariant p M) :
    M*groupedProjection e g p ρ=groupedProjection e g p ρ*M := by
  apply signedConj_commutes p g M _ (invariant_matrix_commutes p M hM g)
  apply blockProjection_central e p ρ
  intro h
  exact invariant_matrix_commutes p M hM (blockPerm e h)

lemma grouped_density_domination [Nonempty A] (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (g : Equiv.Perm (Fin N)) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    [∀i, (ρ i).IsIrreducible] :
    (((∏i, (Module.finrank ℂ (V i):ℂ)*(n i+1:ℂ)^(2*(Fintype.card A)^2))) •
      (∑u : ∀i, LocalDensityIndex p (n i),
        tensorMatrices (fun t => localDensity p (n (groupOf e g t)) (u (groupOf e g t)))) -
      groupedProjection e g p ρ).PosSemidef := by
  have h := signedConj_psd p g _ (block_density_domination e p ρ)
  rw [signedConj_sub_smul_sum] at h
  have he (u : ∀i, LocalDensityIndex p (n i)) :
      signedConj p g (tensorMatrices (fun t => localDensity p (n (ofLex (e.symm t)).1) (u (ofLex (e.symm t)).1))) =
      tensorMatrices (fun t => localDensity p (n (groupOf e g t)) (u (groupOf e g t))) := by
    exact even_tensor_covariance p g _ (fun t => localDensity_even p _ _)
  simpa only [he,groupedProjection] using h

lemma grouped_density_card_bound (p : A → Bool) :
    Fintype.card (∀i, LocalDensityIndex p (n i)) ≤ ∏i, (n i+1)^(2*(Fintype.card A)^2) := by
  rw [Fintype.card_pi]
  exact Finset.prod_le_prod (fun i _ => localDensityIndex_card p (n i))

end BinaryCoordinateSweeps.Signed

end

end OAI
