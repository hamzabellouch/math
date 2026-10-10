import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

universe u

namespace Kadison.SeparableSmall

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem small : Small.{0} H := by
  obtain ⟨F,hF⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X:=H)
  exact small_of_injective hF.injective

local instance separableSmallSmall : Small.{0} H := small H

abbrev Model : Type := Shrink H

instance model_inner : InnerProductSpace ℂ (Model H) where
  inner x y := inner ℂ ((equivShrink H).symm x) ((equivShrink H).symm y)
  conj_inner_symm x y := inner_conj_symm _ _
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner ((equivShrink H).symm x)
  add_left x y z := by
    change inner ℂ (Shrink.linearEquiv ℂ H (x+y)) _ = _
    rw [map_add,inner_add_left]
    rfl
  smul_left x y c := by
    change inner ℂ (Shrink.linearEquiv ℂ H (c • x)) _ = _
    rw [map_smul,inner_smul_left]
    rfl

def unitary : Model H ≃ₗᵢ[ℂ] H where
  toLinearEquiv := Shrink.linearEquiv ℂ H
  norm_map' _ := rfl

instance model_complete : CompleteSpace (Model H) :=
  (unitary H).toIsometryEquiv.completeSpace_iff.mpr inferInstance

instance model_separable : TopologicalSpace.SeparableSpace (Model H) :=
  (unitary H).symm.surjective.denseRange.separableSpace (unitary H).symm.continuous

end Kadison.SeparableSmall

end

end
end

end OAI
