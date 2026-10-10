import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSamplingNonzero

namespace OAI

/-! # Nontrivial height forces the nonzero sampling branch -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

include T hunimod eW in
omit [FiniteDimensional ℝ W] in
/-- With no generator weights, separation makes the height space trivial. -/
theorem nonempty_letters_of_nontrivial_height [Nontrivial W] :
    Nonempty (Fin M.letterCount) := by
  classical
  by_contra hn
  let : IsEmpty (Fin M.letterCount) := not_nonempty_iff.mp hn
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  exact hw ((M.supportIn T hunimod eW).separates w (fun i => isEmptyElim i))

/-- A retained generator gives positive dimension of the root ideal. -/
theorem nonempty_root_coordinates_of_nonempty_letters
    [Nonempty (Fin M.letterCount)] :
    Nonempty (Fin (finrank ℝ (cartanRootIdeal H))) := by
  obtain ⟨i⟩ := ‹Nonempty (Fin M.letterCount)›
  have hi : M.letter i ≠ 0 := by
    intro hz
    have h := M.letter_quotient i
    rw [hz, map_zero] at h
    exact M.abelianBasis.ne_zero i h.symm
  let : Nontrivial (cartanRootIdeal H) := nontrivial_of_ne (M.letter i) 0 hi
  exact Fin.pos_iff_nonempty.mp (Module.finrank_pos (R := ℝ) (M := cartanRootIdeal H))

end PolycyclicRecognition.CartanWordModel

end

end OAI
