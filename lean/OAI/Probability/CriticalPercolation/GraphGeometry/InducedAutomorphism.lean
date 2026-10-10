import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphIso
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced
import OAI.Probability.CriticalPercolation.Criticality.ComponentCritical

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.inducedEdges_mem (phi : G.Aut) (S : Set V)
    (hS : ∀ x, phi.vertex x∈S ↔ x∈S) (e : E) :
    phi.edge e∈G.inducedEdges S ↔ e∈G.inducedEdges S := by
  constructor
  · intro h x hx
    apply (hS x).mp
    apply h (phi.vertex x)
    rw [phi.preserves]
    exact Sym2.mem_map.mpr ⟨x,hx,rfl⟩
  · intro h y hy
    rw [phi.preserves] at hy
    obtain ⟨x,hx,rfl⟩ := Sym2.mem_map.mp hy
    exact (hS x).mpr (h x hx)

lemma Aut.inducedEdges_image (phi : G.Aut) (S : Set V)
    (hS : ∀ x, phi.vertex x∈S ↔ x∈S) :
    phi.edge '' G.inducedEdges S=G.inducedEdges S := by
  ext e
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (Aut.inducedEdges_mem G phi S hS a).mpr ha
  · intro he
    exact ⟨phi.edge.symm e,(Aut.inducedEdges_mem G phi S hS (phi.edge.symm e)).mp
      (by simpa only [Equiv.apply_symm_apply] using he),phi.edge.apply_symm_apply e⟩

def Aut.restrict (phi : G.Aut) (S : Set V)
    (hS : ∀ x, phi.vertex x∈S ↔ x∈S) : (G.induce S).Aut where
  vertex :=
    { toFun := fun x => ⟨phi.vertex x,(hS x).mpr x.property⟩
      invFun := fun x => ⟨phi.vertex.symm x,(hS (phi.vertex.symm x)).mp
        (by simpa only [Equiv.apply_symm_apply] using x.property)⟩
      left_inv := fun x => Subtype.ext (phi.vertex.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (phi.vertex.apply_symm_apply x) }
  edge :=
    { toFun := fun e => ⟨phi.edge e,(Aut.inducedEdges_mem G phi S hS e).mpr e.property⟩
      invFun := fun e => ⟨phi.edge.symm e,(Aut.inducedEdges_mem G phi S hS (phi.edge.symm e)).mp
        (by simpa only [Equiv.apply_symm_apply] using e.property)⟩
      left_inv := fun e => Subtype.ext (phi.edge.symm_apply_apply e)
      right_inv := fun e => Subtype.ext (phi.edge.apply_symm_apply e) }
  preserves e := by
    apply Sym2.map.injective Subtype.val_injective
    rw [G.induce_ends_map,Sym2.map_map]
    change G.ends (phi.edge e.val)=Sym2.map (fun x : S => phi.vertex x.val) ((G.induce S).ends e)
    calc
      G.ends (phi.edge e.val)=Sym2.map phi.vertex (G.ends e.val) := phi.preserves e.val
      _=Sym2.map phi.vertex (Sym2.map (Subtype.val : S → V) ((G.induce S).ends e)) :=
        congrArg (Sym2.map phi.vertex) (G.induce_ends_map S e).symm
      _=_ := Sym2.map_map _

lemma Aut.domainComponent_image (phi : G.Aut) (S : Set V)
    (hS : ∀ x, phi.vertex x∈S ↔ x∈S) (o : V) :
    phi.vertex '' G.domainComponent S o=G.domainComponent S (phi.vertex o) := by
  change phi.vertex '' G.cluster (G.inducedEdges S) o=G.cluster (G.inducedEdges S) (phi.vertex o)
  rw [Aut.cluster_image,Aut.inducedEdges_image G phi S hS]

lemma domainComponent_eq_of_mem (S : Set V) {o x : V} (hx : x∈G.domainComponent S o) :
    G.domainComponent S x=G.domainComponent S o := by
  ext y
  exact ⟨fun h => hx.trans h,fun h => hx.symm.trans h⟩

lemma Aut.preserves_domainComponent (phi : G.Aut) (S : Set V)
    (hS : ∀ x, phi.vertex x∈S ↔ x∈S) (o x : V)
    (hx : x∈G.domainComponent S o) (hpx : phi.vertex x∈G.domainComponent S o) :
    ∀ y, phi.vertex y∈G.domainComponent S o ↔ y∈G.domainComponent S o := by
  have heq : phi.vertex '' G.domainComponent S o=G.domainComponent S o := calc
    phi.vertex '' G.domainComponent S o=phi.vertex '' G.domainComponent S x :=
      congrArg (Set.image phi.vertex) (G.domainComponent_eq_of_mem S hx).symm
    _=G.domainComponent S (phi.vertex x) := Aut.domainComponent_image G phi S hS x
    _=G.domainComponent S o := G.domainComponent_eq_of_mem S hpx
  intro y
  constructor
  · intro hy
    have him : phi.vertex y∈phi.vertex '' G.domainComponent S o := by rwa [heq]
    obtain ⟨z,hz,hzy⟩ := him
    exact phi.vertex.injective hzy ▸ hz
  · intro hy
    rw [←heq]
    exact ⟨y,hy,rfl⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
