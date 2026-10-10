import Mathlib
import OAI.Analysis.Commutator.CompactInvariant

namespace OAI

noncomputable section

section

noncomputable section

open Set

namespace Kadison.CompactInvariant

variable {G X : Type*} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X]

omit [T2Space X] in
lemma invariant_closure {S : Set X} (hS : Invariant (G:=G) S) :
    Invariant (G:=G) (closure S) := by
  intro g x hx
  apply closure_mono (show (fun y : X => g • y) '' S⊆S from by
    rintro _ ⟨y,hy,rfl⟩; exact hS g y hy)
  exact mem_closure_image (continuous_const_smul g).continuousAt hx

omit [TopologicalSpace X] [T2Space X] [ContinuousConstSMul G X] in
lemma invariant_orbit (x : X) : Invariant (G:=G) (MulAction.orbit G x) := by
  intro g y hy
  obtain ⟨h,rfl⟩ := hy
  exact ⟨g*h,mul_smul g h x⟩

omit [T2Space X] in
lemma minimal_orbit_closure {C K : Set X}
    (hK : Minimal (fun S => S⊆C ∧ S.Nonempty ∧ IsClosed S ∧ Invariant (G:=G) S) K)
    {x : X} (hx : x∈K) : closure (MulAction.orbit G x)=K := by
  have ho : MulAction.orbit G x⊆K := by
    rintro y ⟨g,rfl⟩
    exact hK.prop.2.2.2 g x hx
  have hs : closure (MulAction.orbit G x)⊆K := closure_minimal ho hK.prop.2.2.1
  apply hs.antisymm
  apply hK.le_of_le _ hs
  exact ⟨hs.trans hK.prop.1,⟨x,subset_closure ⟨1,one_smul G x⟩⟩,isClosed_closure,
    invariant_closure (invariant_orbit x)⟩

omit [T2Space X] in
lemma minimal_finite_open_cover {C K : Set X} (hcomp : IsCompact K)
    (hK : Minimal (fun S => S⊆C ∧ S.Nonempty ∧ IsClosed S ∧ Invariant (G:=G) S) K)
    {U : Set X} (hU : IsOpen U) (hne : (K∩U).Nonempty) :
    ∃ t : Finset G,K⊆⋃ g∈t,(fun x : X => g • x) ⁻¹' U := by
  apply hcomp.elim_finite_subcover (fun g : G => (fun x : X => g • x) ⁻¹' U)
    (fun g => hU.preimage (continuous_const_smul g))
  intro x hx
  obtain ⟨y,hyK,hyU⟩ := hne
  have hycl : y∈closure (MulAction.orbit G x) := by
    rw [minimal_orbit_closure hK hx]
    exact hyK
  obtain ⟨z,hzU,hzorbit⟩ := mem_closure_iff.mp hycl U hU hyU
  obtain ⟨g,rfl⟩ := hzorbit
  exact mem_iUnion.mpr ⟨g,hzU⟩

end Kadison.CompactInvariant

end

end
end

end OAI
