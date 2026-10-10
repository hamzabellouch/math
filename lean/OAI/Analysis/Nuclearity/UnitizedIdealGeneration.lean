import OAI.Analysis.Nuclearity.IdealInIdeal
import OAI.Analysis.Nuclearity.UnitizedTensorElementary
import OAI.Analysis.Nuclearity.ElementaryGeneratedIdeal

namespace OAI

/-! Transfer of elementary ideal generation from the left unitization to
its original nonunital tensor ideal. -/

noncomputable section
open scoped Topology

namespace WeakPureInfiniteness

universe u
variable {A B : Type u} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

theorem unitizationInr_rightIdeal : RightIdealRange (Unitization.inrNonUnitalStarAlgHom ℂ A) := by
  intro a b
  refine ⟨b.fst • a + a * b.snd, ?_⟩
  change (Unitization.inr (b.fst • a + a * b.snd) : Unitization ℂ A) = Unitization.inr a * b
  apply Unitization.ext
  · simp
  · simp [Unitization.snd_mul]

theorem unitizedTensorInclusion_rightIdeal :
    RightIdealRange (unitizedTensorInclusion (A := A) (B := B)) := by
  have he : unitizedTensorInclusion (A := A) (B := B) =
      minimalMapLeft (C := B) (Unitization.inrNonUnitalStarAlgHom ℂ A) := by
    apply minimalTensor_hom_ext
    intro a b
    rw [unitizedTensorInclusion_elementary, minimalMapLeft_elementary]
    rfl
  rw [he]
  exact unitizationInr_rightIdeal.tensor

theorem elementary_generation_of_unitization
    (hgen : ∀ K : NonunitalClosedIdeal.Ideal (MinimalTensor (Unitization ℂ A) B),
      (elementaryGeneratedIdeal K).module = K.module)
    (J : NonunitalClosedIdeal.Ideal (MinimalTensor A B)) :
    (elementaryGeneratedIdeal J).module = J.module := by
  let j := unitizedTensorInclusion (A := A) (B := B)
  have hj : RightIdealRange j := unitizedTensorInclusion_rightIdeal
  have hinj : Function.Injective j := unitizedTensorInclusion_isometry.injective
  let I := elementaryGeneratedIdeal J
  let K := idealInIdealImage j hj J
  let L := idealInIdealImage j hj I
  have hKL : (elementaryGeneratedIdeal K).module ≤ L.module := by
    apply closure_minimal ?_ L.closed
    apply Submodule.span_le.mpr
    rintro w ⟨a, b, rfl, hab⟩
    by_cases hb : b = 0
    · subst b
      have hz : minimalElementary a (0 : B) = 0 := map_zero (minimalElementaryRightLinear a)
      rw [hz]
      exact L.module.zero_mem
    · obtain ⟨z, hzJ, hze⟩ := (mem_idealInIdealImage j hj J _).mp hab
      obtain ⟨x, rfl⟩ := unitizedTensor_elementary_lift a b hb ⟨z, hze⟩
      have hx : minimalElementary x b ∈ J.module := by
        have he : j (minimalElementary x b) = j z := by
          rw [hze]
          exact unitizedTensorInclusion_elementary x b
        exact hinj he ▸ hzJ
      apply (mem_idealInIdealImage j hj I _).mpr
      exact ⟨minimalElementary x b, elementary_mem_generatedIdeal J x b hx,
        unitizedTensorInclusion_elementary x b⟩
  apply le_antisymm (elementaryGeneratedIdeal_le J)
  intro z hz
  have hjz : j z ∈ K.module := (mem_idealInIdealImage j hj J _).mpr ⟨z, hz, rfl⟩
  have hLz : j z ∈ L.module := hKL (by rwa [hgen K])
  obtain ⟨w, hw, he⟩ := (mem_idealInIdealImage j hj I _).mp hLz
  exact hinj he ▸ hw

end WeakPureInfiniteness

end

end OAI
