import OAI.Analysis.Hyperinvariant.Specification

namespace OAI

namespace Hyperinvariant
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Triviality of invariant projections in a von Neumann algebra implies
hyperinvariant-subspace triviality in the entire bounded-operator algebra. -/
theorem transitiveCommutant_of_invariantProjections
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) (hT : T ∈ M)
    (hproj : ∀ p ∈ M, IsStarProjection p → (1 - p) * T * p = 0 →
      p = 0 ∨ p = 1) : TransitiveCommutant T := by
  intro K hK hInv
  let : CompleteSpace K := hK.completeSpace_coe
  have hp : IsStarProjection K.starProjection := isStarProjection_starProjection
  have hpM : K.starProjection ∈ M := by
    apply (VonNeumannAlgebra.IsStarProjection.mem_iff hp M).2
    intro A hA
    rw [Submodule.range_starProjection]
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    exact hInv A ((VonNeumannAlgebra.mem_commutant_iff.mp hA) T hT).symm
  have hi : (1 - K.starProjection) * T * K.starProjection = 0 := by
    ext x
    have hm : T (K.starProjection x) ∈ K :=
      hInv T rfl _ (K.starProjection_apply_mem x)
    simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self, zero_apply]
    exact sub_eq_zero.mpr (Submodule.starProjection_eq_self_iff.mpr hm).symm
  rcases hproj K.starProjection hpM hp hi with hz | ho
  · left
    apply le_antisymm _ bot_le
    intro x hx
    have hf : K.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
    have he : K.starProjection x = 0 := congrArg (fun A : H →L[ℂ] H => A x) hz
    exact hf.symm.trans he
  · right
    apply le_antisymm le_top
    intro x _
    have he : K.starProjection x = x := congrArg (fun A : H →L[ℂ] H => A x) ho
    have hm := K.starProjection_apply_mem x
    rwa [he] at hm

end Hyperinvariant

end OAI
