import OAI.Analysis.IrrationalRotation.Operators.Conjugation
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

noncomputable section
namespace Invariant233
open scoped lp

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_conjugation_fixing_hilbertBasis (b : HilbertBasis ι ℂ H) :
    ∃ C : HilbertConjugation H, ∀ i, C.val (b i) = b i := by
  classical
  let C : H → H := fun x => b.repr.symm (star (b.repr x))
  have hC : IsConjugation C := by
    refine ⟨fun x => ?_, fun x y => ?_, fun c x => ?_, fun x => ?_⟩
    · simp [C]
    · simp [C]
    · simp [C]
    · simp [C]
  refine ⟨hC.toHilbertConjugation, fun i => ?_⟩
  change b.repr.symm (star (b.repr (b i))) = b i
  rw [b.repr_self]
  have hs : star (lp.single 2 i (1 : ℂ) : ℓ²(ι, ℂ)) = lp.single 2 i (1 : ℂ) := by
    ext j
    by_cases hij : j = i
    · subst j; simp [lp.single_apply]
    · simp [lp.single_apply, Pi.single_eq_of_ne hij]
  rw [hs, b.repr_symm_single]

theorem nonempty_hilbertConjugation [CompleteSpace H] : Nonempty (HilbertConjugation H) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  obtain ⟨C, _⟩ := exists_conjugation_fixing_hilbertBasis b
  exact ⟨C⟩

theorem exists_isConjugation [CompleteSpace H] : ∃ C : H → H, IsConjugation C := by
  obtain ⟨C⟩ := nonempty_hilbertConjugation (H := H)
  exact ⟨C.val, C.isConjugation⟩

end Invariant233

end

end OAI
