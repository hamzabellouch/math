import OAI.Dynamics.EntropyCounterexample.CoordinateGoodCover
import OAI.Geometry.SingularHomology.TetrahedronGoodCover
import OAI.Geometry.SingularHomology.TetrahedronRadialHomeomorph

namespace OAI

noncomputable section

namespace Problem340

open SimplicialSphere CoordinateGoodCover

def tetrahedronGoodCover : GoodCover (Fin 4) TopologicalBoundary where
  carrier := vertexStar
  isOpen := isOpen_vertexStar
  covers p := by
    have hp : p ∈ ⋃ i : Fin 4, vertexStar i := by
      rw [vertexStar_cover]
      exact Set.mem_univ p
    exact Set.mem_iUnion.mp hp
  contractible s hs hne := by
    rw [← starIntersection_eq_biInter] at hne ⊢
    exact contractible_starIntersection s hs ((starIntersection_nonempty_iff s).mp hne)

def tetrahedralSphereGoodCover : GoodCover (Fin 4) StandardSphere2 where
  carrier i := radialHomeomorph.symm ⁻¹' vertexStar i
  isOpen i := (isOpen_vertexStar i).preimage radialHomeomorph.symm.continuous
  covers p := tetrahedronGoodCover.covers (radialHomeomorph.symm p)
  contractible s hs hne := by
    have heq : (⋂ i ∈ s, radialHomeomorph.symm ⁻¹' vertexStar i) =
        radialHomeomorph.symm ⁻¹' starIntersection s := by
      ext p
      simp [starIntersection]
    rw [heq] at hne ⊢
    apply contractible_starPreimage radialHomeomorph.symm s hs
    apply (starIntersection_nonempty_iff s).mp
    obtain ⟨p, hp⟩ := hne
    exact ⟨radialHomeomorph.symm p, hp⟩

theorem tetrahedralSphereGoodCover_list_nonempty_iff
    {ι : Type*} [Fintype ι] (v : ι → Fin 4) :
    (⋂ i, tetrahedralSphereGoodCover.carrier (v i)).Nonempty ↔
      ¬ Function.Surjective v := by
  have h : (⋂ i, tetrahedralSphereGoodCover.carrier (v i)).Nonempty ↔
      (⋂ i, vertexStar (v i)).Nonempty := by
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨radialHomeomorph.symm p, by simpa only [tetrahedralSphereGoodCover, Set.mem_iInter, Set.mem_preimage,
        Homeomorph.symm_apply_apply] using hp⟩
    · rintro ⟨p, hp⟩
      exact ⟨radialHomeomorph p, by simpa only [tetrahedralSphereGoodCover, Set.mem_iInter, Set.mem_preimage,
        Homeomorph.symm_apply_apply] using hp⟩
  exact h.trans (vertexStar_list_nonempty_iff v)

end Problem340

end

end OAI
