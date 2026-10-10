import OAI.MeasureTheory.Falconer.Estimates.PrefixCenters

namespace OAI

/-! Realize a finite planar path set by its actual dyadic centers, with an
exact inverse coding. Prefix masses and cardinalities are unchanged. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem planar_path_center_realization {N : ℕ} (Q : DyadicCube 2) (hQ : 0 < Q.side)
    (L : Finset (CellPath 2)) (hL : L ⊆ cubePaths 2 N) :
    ∃ l : Space 2 → CellPath 2,
      let P := L.image (fun p => (Q.descendant p).center)
      (∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier) ∧
      Set.InjOn l (P : Set (Space 2)) ∧ P.image l = L ∧
      FiniteSeparatedAt (Q.side/(2:ℝ)^N) P := by
  let C := fun p : CellPath 2 => (Q.descendant p).center
  have hC : Set.InjOn C (L : Set (CellPath 2)) := by
    intro p hp q hq he
    exact Q.center_injective_at_depth hQ ((mem_cubePaths _ _ _).mp (hL hp))
      ((mem_cubePaths _ _ _).mp (hL hq)) he
  let l := Function.invFunOn C (L : Set (CellPath 2))
  have hl (p : CellPath 2) (hp : p ∈ L) : l (C p) = p := hC.leftInvOn_invFunOn hp
  refine ⟨l,?_,?_,?_,?_⟩
  · intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    rw [hl p hp]
    exact ⟨hL hp,(Q.descendant p).center_mem (Q.descendant_side_pos hQ p)⟩
  · intro x hx y hy he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
    rw [hl p hp,hl q hq] at he
    exact congrArg C he
  · ext p
    constructor
    · intro hp
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
      rwa [hl q hq]
    · intro hp
      exact Finset.mem_image.mpr ⟨C p,Finset.mem_image_of_mem C hp,hl p hp⟩
  · intro x hx y hy hxy
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
    exact Q.centers_separated hQ ((mem_cubePaths _ _ _).mp (hL hp))
      ((mem_cubePaths _ _ _).mp (hL hq)) (fun he => hxy (congrArg C he))

end Falconer

end OAI
