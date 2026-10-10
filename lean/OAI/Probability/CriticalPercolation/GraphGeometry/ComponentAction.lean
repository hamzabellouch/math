import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.RestrictedAction

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E Λ T : Type*} (G : BondGraph V E)
  [Group Λ] [Group T] [MulAction Λ V] [MulAction Λ E]

def componentKernel (a : Λ →* T) (C : Set V) : Subgroup Λ :=
  a.ker ⊓ domainPreserver C

lemma componentKernel_le (a : Λ →* T) (C : Set V) :
    componentKernel a C≤domainPreserver C := inf_le_right

lemma componentKernel_same_level
    (ha : G.PreservesEnds (Λ := Λ)) (a : Λ →* T) (z : V → T)
    (hz : ∀ g v, z (g • v)=a g*z v)
    (Q : Set T) (o : V) (x y : G.domainComponent (z ⁻¹' Q) o)
    (horbit : y.val∈MulAction.orbit Λ x.val) (hlevel : z y.val=z x.val) :
    ∃ g : componentKernel a (G.domainComponent (z ⁻¹' Q) o),
      (g.val : Λ) • x.val=y.val := by
  obtain ⟨g,hg⟩ := EquivariantCoordinates.same_level_kernel_orbit a z hz x.val y.val horbit hlevel
  change g.val • x.val=y.val at hg
  have hS : ∀ v, (G.smulAut ha g.val).vertex v∈z ⁻¹' Q ↔ v∈z ⁻¹' Q := by
    intro v
    change z (g.val • v)∈Q ↔ z v∈Q
    rw [hz,g.property,one_mul]
  have hp := Aut.preserves_domainComponent G (G.smulAut ha g.val) (z ⁻¹' Q)
    hS o x.val x.property (by change g.val • x.val∈_; rw [hg]; exact y.property)
  exact ⟨⟨g.val,g.property,hp⟩,hg⟩

theorem componentKernel_finite_orbits
    (ha : G.PreservesEnds (Λ := Λ))
    (R : Set V) (hR : R.Finite) (hcover : ∀ v, ∃ s∈R, v∈MulAction.orbit Λ s)
    (a : Λ →* T) (z : V → T) (hz : ∀ g v, z (g • v)=a g*z v)
    (Q : Set T) (hQ : Q.Finite) (o : V) (ho : z o∈Q) :
    let C := G.domainComponent (z ⁻¹' Q) o
    let L := componentKernel a C
    let _ := restrictedVertexAction C L (componentKernel_le a C)
    ∃ S : Set C, S.Finite ∧ ∀ v : C, ∃ s∈S, v∈MulAction.orbit L s := by
  let C := G.domainComponent (z ⁻¹' Q) o
  let L := componentKernel a C
  let _ := restrictedVertexAction C L (componentKernel_le a C)
  let I : Set (V×T) := {q | q.1∈R ∧ q.2∈Q ∧ ∃ x : C,
    x.val∈MulAction.orbit Λ q.1 ∧ z x.val=q.2}
  have hI : I.Finite := (hR.prod hQ).subset (fun _ h => ⟨h.1,h.2.1⟩)
  let _ := hI.to_subtype
  have hex : ∀ q : I, ∃ x : C, x.val∈MulAction.orbit Λ q.val.1 ∧ z x.val=q.val.2 :=
    fun q => q.property.2.2
  choose r hr using hex
  refine ⟨Set.range r,Set.finite_range r,?_⟩
  intro y
  obtain ⟨s,hs,hys⟩ := hcover y.val
  have hyQ : z y.val∈Q := G.domainComponent_subset ho y.property
  let q : I := ⟨(s,z y.val),hs,hyQ,y,hys,rfl⟩
  refine ⟨r q,⟨q,rfl⟩,?_⟩
  have hyorbit : y.val∈MulAction.orbit Λ (r q).val := by
    rw [MulAction.orbit_eq_iff.mpr (hr q).1]
    exact hys
  obtain ⟨g,hg⟩ := G.componentKernel_same_level ha a z hz Q o (r q) y hyorbit (hr q).2.symm
  exact ⟨g,Subtype.ext hg⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
