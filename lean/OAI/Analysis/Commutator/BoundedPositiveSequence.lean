import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped BoundedContinuousFunction

namespace Kadison.BoundedPositiveSequence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {ι : Type*} [TopologicalSpace ι] [DiscreteTopology ι]

theorem squareRoot (d : ι →ᵇ A) (hd : ∀ i, 0≤d i) :
    ∃ z : ι →ᵇ A, d=star z*z := by
  let z : ι →ᵇ A := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun i => CFC.sqrt (d i)) (Real.sqrt ‖d‖) (fun i => by
      rw [CFC.norm_sqrt _ (hd i)]
      exact Real.sqrt_le_sqrt (d.norm_coe_le_norm i))
  refine ⟨z,?_⟩
  apply BoundedContinuousFunction.ext
  intro i
  change d i=star (CFC.sqrt (d i))*CFC.sqrt (d i)
  rw [(CFC.sqrt_nonneg (d i)).star_eq,CFC.sqrt_mul_sqrt_self _ (hd i)]

lemma map_nonneg {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (φ : (ι →ᵇ A) →⋆ₐ[ℂ] B) (d : ι →ᵇ A) (hd : ∀ i, 0≤d i) : 0≤φ d := by
  obtain ⟨z,rfl⟩ := squareRoot d hd
  simpa only [map_mul,map_star] using star_mul_self_nonneg (φ z)

end Kadison.BoundedPositiveSequence

end

end
end

end OAI
