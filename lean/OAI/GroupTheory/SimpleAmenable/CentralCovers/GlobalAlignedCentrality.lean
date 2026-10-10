import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveCentralLaws

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section GlobalAlignedCentrality

variable {H Q ι : Type*} [Group H] [Group Q]

theorem CentralOn.iSup_directed (q : H →* Q) (S : ι → Subgroup H) [Nonempty ι]
    (hd : Directed (· ≤ ·) S) (h : ∀ i, CentralOn q (S i)) : CentralOn q (⨆ i, S i) := by
  rw [centralOn_iff]
  intro x hx hqx y hy
  obtain ⟨i,hi⟩ := (Subgroup.mem_iSup_of_directed hd).mp hx
  obtain ⟨j,hj⟩ := (Subgroup.mem_iSup_of_directed hd).mp hy
  obtain ⟨k,hik,hjk⟩ := hd i j
  exact (centralOn_iff q (S k)).mp (h k) x (hik hi) hqx y (hjk hj)

theorem centralOn_iSup_of_finite (q : H →* Q) (S : ι → Subgroup H)
    (h : ∀ F : Finset ι, CentralOn q (⨆ i : F, S i.val)) : CentralOn q (⨆ i, S i) := by
  classical
  let T : Finset ι → Subgroup H := fun F => ⨆ i : F, S i.val
  have hmono : Monotone T := by
    intro F F' hFF'
    apply iSup_le
    intro i
    exact le_iSup (fun j : F' => S j.val) ⟨i.val,hFF' i.property⟩
  have hdir : Directed (· ≤ ·) T := fun F F' =>
    ⟨F ∪ F',hmono Finset.subset_union_left,hmono Finset.subset_union_right⟩
  have he : (⨆ F, T F) = ⨆ i, S i := by
    apply le_antisymm
    · apply iSup_le
      intro F
      exact iSup_le (fun i => le_iSup S i.val)
    · apply iSup_le
      intro i
      exact (le_iSup (fun j : ({i} : Finset ι) => S j.val) ⟨i,Finset.mem_singleton_self i⟩).trans
        (le_iSup T {i})
  rw [← he]
  exact CentralOn.iSup_directed q T hdir h

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem polygonStars_central :
    CentralOn (coverMap M (alternatingGenerator a r m hm))
      (⨆ V : polygonAlgebra a, (B.polygonStar hlarge h hr V).range) := by
  apply centralOn_iSup_of_finite
  intro F
  exact B.polygonStars_finite_central hlarge h hr (fun V : F => V.val)

theorem polygonStar_control (V W : polygonAlgebra a) (hVW : V ≤ W) :
    SameActionOn (B.polygonStar hlarge h hr W)
      (B.c.comp (universalProjection (alternatingGroup (Fin (m+1)))))
      (B.polygonStar hlarge h hr V).range := by
  let R : Bool → polygonAlgebra a := fun b => if b then W else V
  obtain ⟨S,hS⟩ := polygon_family_primitive_resolution r hr R
  have hV := hS false
  have hW := hS true
  change ResolvedBy _ V.val at hV
  change ResolvedBy _ W.val at hW
  rw [B.polygonStar_eq hlarge h hr (fun p : S => p.val) V hV,
    B.polygonStar_eq hlarge h hr (fun p : S => p.val) W hW]
  exact B.fullGeometricSector_control hlarge _ _ V W hVW

theorem polygonStar_empty : B.polygonStar hlarge h hr ⊥ = 1 := by
  apply CentralOn.lift_unique (coverMap M (alternatingGenerator a r m hm))
    (⨆ V : polygonAlgebra a, (B.polygonStar hlarge h hr V).range)
    (B.polygonStars_central hlarge h hr)
  · exact le_iSup (fun V : polygonAlgebra a => (B.polygonStar hlarge h hr V).range) ⊥
  · rintro x ⟨s,rfl⟩
    exact Subgroup.one_mem _
  · rw [B.polygonStar_projection hlarge h hr]
    ext s : 1
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro p
    change conditionalPerm (⊥ : polygonAlgebra a) (universalProjection _ s).val p = p
    simp [conditionalPerm]

end InitialCoverSystem

theorem polygon_law_cover_eventually {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (ha : 0<a) (hlarge : 25 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hSlope : 8000<ordinary (cutTau^a)) (hconj : |conjugate (cutTau^a)|<1/1000) :
    ∃ L : ℕ, ∀ M : ℕ, L≤M → ∃ B : InitialCoverSystem a r m hm M, B.AllPrimitiveLaws := by
  obtain ⟨L₁,hL₁⟩ := initialCoverSystem_eventually a r m hm hr (by omega)
  obtain ⟨L₂,hL₂⟩ := primitive_laws_eventually ha hlarge hr hSlope hconj
  refine ⟨max L₁ L₂,fun M hM => ?_⟩
  obtain ⟨B⟩ := hL₁ M ((le_max_left _ _).trans hM)
  exact ⟨B,hL₂ M ((le_max_right _ _).trans hM) B⟩

end GlobalAlignedCentrality

end SimpleAmenable
end
end

end OAI
