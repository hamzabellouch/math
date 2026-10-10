import OAI.NumberTheory.Ostmann.QuadraticCenter.ConductorKernelCandidates
import OAI.NumberTheory.Ostmann.Construction.RetainedCharacterPrimeBound
import OAI.NumberTheory.Ostmann.QuadraticCenter.ExceptionalKernelFamilyBound

namespace OAI

/-! # Removing the kernel family of a large Page character -/

namespace Ostmann

open scoped Classical

noncomputable def pageKernelExclusion (P : PublishedProgressionInput) (Q : ℕ) (R : ℝ) : Finset ℤ :=
  match selectedPageZero P Q with
  | none => ∅
  | some e => if R < (e.modulus : ℝ) then largeConductorKernelCandidates e.modulus else ∅

/-- A kernel outside the explicit excluded family can only represent a
selected Page character whose conductor is at most the retained threshold. -/
theorem page_kernel_retention (P : PublishedProgressionInput) (Q : ℕ) (R : ℝ)
    (d : ℤ) (χ : PrimitiveRealCharacter) (N : ℕ) (hN : 0 < N)
    (hNq : N ∣ χ.modulus) (hqN : χ.modulus ≤ 8 * N)
    (hdN : d.natAbs = N ∨ d.natAbs = 2 * N) (hqd : χ.modulus ≤ 4 * d.natAbs)
    (hout : d ∉ pageKernelExclusion P Q R)
    (e : PrimitiveRealZero) (he : selectedPageZero P Q = some e)
    (hsame : samePrimitiveRealCharacter e χ) : (e.modulus : ℝ) ≤ R := by
  by_contra hnot
  have hlarge : R < (e.modulus : ℝ) := lt_of_not_ge hnot
  have hmem : d ∈ largeConductorKernelCandidates e.modulus := by
    rw [hsame.1]
    exact mem_largeConductorKernelCandidates d χ.modulus N hN χ.positive hNq hqN hdN hqd
  have heq : pageKernelExclusion P Q R = largeConductorKernelCandidates e.modulus := by
    simp only [pageKernelExclusion, he, ite_eq_left hlarge]
  exact hout (heq ▸ hmem)

/-- The empty case costs nothing; the only nonempty case is one of the
already-bounded conductor families above the threshold. -/
theorem page_kernel_exclusion_count (P : PublishedProgressionInput) (Q : ℕ) (R E : ℝ)
    (S T : Finset ℤ) (f g : ℤ → ℤ) (hE : 0 ≤ E)
    (hcount : ∀ q : ℕ, R < (q : ℝ) →
      (((S.product T).filter fun z => f z.1 * g z.2 ∈ largeConductorKernelCandidates q).card : ℝ) ≤ E) :
    (((S.product T).filter fun z => f z.1 * g z.2 ∈ pageKernelExclusion P Q R).card : ℝ) ≤ E := by
  cases he : selectedPageZero P Q with
  | none => simpa only [pageKernelExclusion, he, Finset.notMem_empty, Finset.filter_false,
      Finset.card_empty, Nat.cast_zero] using hE
  | some e =>
    by_cases hlarge : R < (e.modulus : ℝ)
    · simpa only [pageKernelExclusion, he, ite_eq_left hlarge] using hcount e.modulus hlarge
    · simpa only [pageKernelExclusion, he, ite_eq_right hlarge, Finset.notMem_empty,
        Finset.filter_false, Finset.card_empty, Nat.cast_zero] using hE

end Ostmann

end OAI
