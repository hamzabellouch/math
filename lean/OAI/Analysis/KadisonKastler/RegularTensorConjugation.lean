import OAI.Analysis.KadisonKastler.RegularTensorGap

namespace OAI

/-! # Small changes of position for the actual regular tensor algebra -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem pull_commutant {M N : VonNeumannAlgebra H}
    {u : unitary (H →L[ℂ] H)} (hu : Conjugates u M N)
    {z : H →L[ℂ] H} (hz : z ∈ N.commutant) :
    unitaryConj (star u) z ∈ M.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro x hx
  have hux : unitaryConj u x ∈ N := by
    change unitaryConj u x ∈ (N : Set (H →L[ℂ] H))
    rw [← hu]
    exact Set.mem_image_of_mem _ hx
  have he := congrArg (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (star u))
    (VonNeumannAlgebra.mem_commutant_iff.mp hz _ hux)
  rw [map_mul, map_mul] at he
  change unitaryConj (star u) (unitaryConj u x) * unitaryConj (star u) z =
    unitaryConj (star u) z * unitaryConj (star u) (unitaryConj u x) at he
  simpa only [unitaryConj_star_unitaryConj] using he

private theorem constant_conjugation (u : unitary (H →L[ℂ] H)) (z : H →L[ℂ] H) :
    unitaryConj (regularConstantUnitary u) (regularConstantHom volume z) =
      regularConstantHom volume (unitaryConj u z) := by
  change regularConstantHom volume (u : H →L[ℂ] H) * regularConstantHom volume z *
      star (regularConstantHom volume (u : H →L[ℂ] H)) =
    regularConstantHom volume ((u : H →L[ℂ] H) * z * star (u : H →L[ℂ] H))
  rw [map_mul, map_mul, StarHomClass.map_star]

private theorem conjugate_tensor_mem {M N : VonNeumannAlgebra H}
    {u : unitary (H →L[ℂ] H)} (hu : Conjugates u M N)
    {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H} (hT : T ∈ regularTensorAlgebra M) :
    unitaryConj (regularConstantUnitary u) T ∈ regularTensorAlgebra N := by
  apply (mem_regularTensorAlgebra_iff N _).mpr
  intro z hz
  have he := (mem_regularTensorAlgebra_iff M T).mp hT _ (pull_commutant hu hz)
  have hs : regularConstantUnitary (star u) = star (regularConstantUnitary u) :=
    map_inv regularConstantUnitary u
  rw [← constant_conjugation, hs] at he
  have hh := congrArg (Unitary.conjStarAlgAut ℂ _ (regularConstantUnitary u)) he
  rw [map_mul, map_mul] at hh
  change unitaryConj (regularConstantUnitary u)
      (unitaryConj (star (regularConstantUnitary u)) (regularConstantHom volume z)) *
      unitaryConj (regularConstantUnitary u) T =
    unitaryConj (regularConstantUnitary u) T * unitaryConj (regularConstantUnitary u)
      (unitaryConj (star (regularConstantUnitary u)) (regularConstantHom volume z)) at hh
  simpa only [← unitaryConj_mul, Unitary.mul_star_self, unitaryConj_one] using hh

theorem Conjugates.regularTensor {M N : VonNeumannAlgebra H}
    {u : unitary (H →L[ℂ] H)} (hu : Conjugates u M N) :
    Conjugates (regularConstantUnitary u) (regularTensorAlgebra M) (regularTensorAlgebra N) := by
  apply Set.ext
  intro T
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact conjugate_tensor_mem hu hS
  · intro hT
    have hS := conjugate_tensor_mem hu.symm hT
    have hs : regularConstantUnitary (star u) = star (regularConstantUnitary u) :=
      map_inv regularConstantUnitary u
    rw [hs] at hS
    refine ⟨unitaryConj (star (regularConstantUnitary u)) T, hS, ?_⟩
    simp only [← unitaryConj_mul, Unitary.mul_star_self, unitaryConj_one]

theorem norm_regularConstantUnitary_sub_one (u : unitary (H →L[ℂ] H)) :
    ‖(regularConstantUnitary u : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) - 1‖ ≤
      ‖(u : H →L[ℂ] H) - 1‖ := by
  change ‖regularConstantHom volume (u : H →L[ℂ] H) - 1‖ ≤ _
  rw [← map_one (regularConstantHom volume), ← map_sub]
  exact NonUnitalStarAlgHom.norm_apply_le (regularConstantHom volume) _

/-- Moving a factor by `u` costs at most twice the displacement in the
regular tensor gap, just as it does in the original representation. -/
theorem kkDistance_regularTensor_conjugate_le (M N : VonNeumannAlgebra H)
    (u : unitary (H →L[ℂ] H)) :
    kkDistance (regularTensorAlgebra N) (regularTensorAlgebra (unitaryConjugateAlgebra u M)) ≤
      kkDistance (regularTensorAlgebra N) (regularTensorAlgebra M) +
        2 * ‖(u : H →L[ℂ] H) - 1‖ := by
  have hg := kkDistance_conjugate_le
    (M := regularTensorAlgebra N) (conjugates_unitaryConjugateAlgebra u M).regularTensor
  have hn := norm_regularConstantUnitary_sub_one u
  linarith

end

end KadisonKastler

end OAI
