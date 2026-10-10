import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace OAI

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem hyperinvariant_projection_mem
    (M : VonNeumannAlgebra H) {T p : H →L[ℂ] H}
    (hT : T ∈ M) (hp : IsStarProjection p)
    (hhyper : ∀ A : H →L[ℂ] H, Commute A T →
      p.range ∈ Module.End.invtSubmodule A) :
    p ∈ M ∧ (1 - p) * T * p = 0 := by
  constructor
  · apply (VonNeumannAlgebra.IsStarProjection.mem_iff hp M).2
    intro A hA
    apply hhyper A
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hA T hT).symm
  · have h := (ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff
      hp.isIdempotentElem).mp
      (hhyper T (Commute.refl T))
    change p * T * p = T * p at h
    rw [sub_mul, one_mul, sub_mul, h, sub_self]

theorem hyperinvariant_subspace_projection_mem
    (M : VonNeumannAlgebra H) {T : H →L[ℂ] H}
    (hT : T ∈ M) (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (hhyper : ∀ A : H →L[ℂ] H, Commute A T →
      S ∈ Module.End.invtSubmodule A) :
    S.starProjection ∈ M ∧ (1 - S.starProjection) * T * S.starProjection = 0 := by
  apply hyperinvariant_projection_mem M hT isStarProjection_starProjection
  simpa only [Submodule.range_starProjection] using hhyper

theorem hyperinvariant_subspace_trivial
    (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T ∈ M)
    (htrivial : ∀ p : H →L[ℂ] H, p ∈ M → IsStarProjection p →
      (1 - p) * T * p = 0 → p = 0 ∨ p = 1)
    (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (hhyper : ∀ A : H →L[ℂ] H, Commute A T →
      S ∈ Module.End.invtSubmodule A) : S = ⊥ ∨ S = ⊤ := by
  obtain ⟨hmem, hinv⟩ := hyperinvariant_subspace_projection_mem M hT S hhyper
  rcases htrivial S.starProjection hmem isStarProjection_starProjection hinv with h0 | h1
  · left
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    have h := (S.starProjection_eq_self_iff).mpr hx
    simpa only [h0, zero_apply] using h.symm
  · right
    apply Submodule.eq_top_iff'.mpr
    intro x
    have h := Submodule.starProjection_apply_mem S x
    simpa only [h1, one_apply_eq_self] using h

theorem closed_hyperinvariant_subspace_trivial
    (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T ∈ M)
    (htrivial : ∀ p : H →L[ℂ] H, p ∈ M → IsStarProjection p →
      (1 - p) * T * p = 0 → p = 0 ∨ p = 1)
    (S : ClosedSubmodule ℂ H)
    (hhyper : ∀ A : H →L[ℂ] H, Commute A T →
      S.toSubmodule ∈ Module.End.invtSubmodule A) :
    S.toSubmodule = ⊥ ∨ S.toSubmodule = ⊤ := by
  exact hyperinvariant_subspace_trivial M hT htrivial S.toSubmodule hhyper

end Invariant233

end OAI
