import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinRows

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries TemplateOneSidedPrior PrimeDyadicCover
attribute [local instance] Classical.propDecidable

theorem oneSidedMean_congr_of_long_mass {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → ℝ) (ν : κ → ℝ) (U : ι → ℂ) (V : κ → ℂ)
    (F G : ι → κ → ℂ) (h : ∀ x, μ x ≠ 0 → ∀ j, F x j = G x j) :
    oneSidedMean μ ν U V F = oneSidedMean μ ν U V G := by
  unfold oneSidedMean
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hμ : μ x = 0
  · simp only [hμ, Complex.ofReal_zero, zero_mul]
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [h x hμ j]

theorem sourceRowMass_ne_zero_exists_source {A : ℕ} (Q H : ℕ)
    (E : Finset (PrimeUpTo A)) (i : Index H)
    (x : Fin Q × Fin (2*lower Q H i+1))
    (hx : sourceRowMass Q H E i x ≠ 0) :
    ∃ p : PrimeUpTo A, p ∈ E ∧ p.val = rowValue Q (2*lower Q H i+1) x := by
  have hm : rowValue Q (2*lower Q H i+1) x ∈ block Q H (sourceNaturals E) i := by
    by_contra hn
    exact hx (by simp only [sourceRowMass, rowMass, ite_eq_right hn])
  exact Finset.mem_image.mp (block_subset Q H (sourceNaturals E) i hm)

theorem source_oneSidedMean_eq_extension {A : ℕ} {κ : Type*} [Fintype κ]
    (Q H : ℕ) (E : Finset (PrimeUpTo A)) (i : Index H)
    (q : κ → ℕ) (χ : ∀ j, MulChar (ZMod (q j)) ℂ)
    (ν : κ → ℝ) (U : Fin Q × Fin (2*lower Q H i+1) → ℂ) (V : κ → ℂ)
    (F : PrimeUpTo A → κ → ℂ) (W : Fin Q → ℕ → κ → ℂ)
    (hW : ∀ x : Fin Q × Fin (2*lower Q H i+1),
      sourceRowMass Q H E i x ≠ 0 → ∀ j,
      sourceRowAmplitude Q F x.1 x.2 j = W x.1 x.2 j) :
    oneSidedMean (sourceRowMass Q H E i) ν U V
      (rowCharacterKernel q χ Q (2*lower Q H i+1) (fun r : Fin Q => r.val)
        (sourceRowAmplitude Q F)) =
    oneSidedMean (sourceRowMass Q H E i) ν U V
      (rowCharacterKernel q χ Q (2*lower Q H i+1) (fun r : Fin Q => r.val) W) := by
  apply oneSidedMean_congr_of_long_mass
  intro x hx j
  simp only [rowCharacterKernel, primeCharacterKernel, hW x hx j]

theorem source_oneSidedMean_eq_extension_on_source {A : ℕ} {κ : Type*} [Fintype κ]
    (Q H : ℕ) (E : Finset (PrimeUpTo A)) (i : Index H)
    (q : κ → ℕ) (χ : ∀ j, MulChar (ZMod (q j)) ℂ)
    (ν : κ → ℝ) (U : Fin Q × Fin (2*lower Q H i+1) → ℂ) (V : κ → ℂ)
    (F : PrimeUpTo A → κ → ℂ) (W : Fin Q → ℕ → κ → ℂ)
    (hW : ∀ p ∈ E, ∀ r : Fin Q, ∀ n : ℕ, Q*n+r.val = p.val →
      ∀ j, W r n j = F p j) :
    oneSidedMean (sourceRowMass Q H E i) ν U V
      (rowCharacterKernel q χ Q (2*lower Q H i+1) (fun r : Fin Q => r.val)
        (sourceRowAmplitude Q F)) =
    oneSidedMean (sourceRowMass Q H E i) ν U V
      (rowCharacterKernel q χ Q (2*lower Q H i+1) (fun r : Fin Q => r.val) W) := by
  apply source_oneSidedMean_eq_extension
  intro x hx j
  obtain ⟨p, hp, he⟩ := sourceRowMass_ne_zero_exists_source Q H E i x hx
  have he' : Q*x.2.val+x.1.val = p.val := he.symm
  rw [sourceRowAmplitude, he', sourceTest_val, hW p hp x.1 x.2 he' j]

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
