import OAI.Analysis.KadisonSimilarity.Representation.GlobalFiberRestriction

namespace OAI

/-! # Everywhere-defined fields and conull unitization -/

namespace KadisonKastler

open KadisonSimilarity

noncomputable section

variable {X A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem zeroExtend_starLift_univ (ρ : X → B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : X) :
    zeroExtendNonunitalRepresentation Set.univ
      (fun y => Unitization.starLift (ρ y.val)) x = ρ x := by
  classical
  unfold zeroExtendNonunitalRepresentation
  rw [dite_eq_left (Set.mem_univ x)]
  change Unitization.starLift.symm (Unitization.starLift (ρ x)) = ρ x
  exact Unitization.starLift.left_inv (ρ x)

theorem zeroExtend_restrict_starLift_univ (ρ : X → B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (ι : A →⋆ₐ[ℂ] B) (x : X) :
    zeroExtendNonunitalRepresentation Set.univ
      (fun y => unitizationRestrict ι (Unitization.starLift (ρ y.val))) x =
      (ρ x).comp ι.toNonUnitalStarAlgHom := by
  rw [zeroExtend_unitizationRestrict, zeroExtend_starLift_univ]

end

end KadisonKastler

end OAI
