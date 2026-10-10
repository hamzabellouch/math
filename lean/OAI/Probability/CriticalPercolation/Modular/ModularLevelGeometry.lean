import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.ComponentAction
import OAI.Probability.CriticalPercolation.Modular.Unimodularity
import OAI.Probability.CriticalPercolation.Modular.ModularCharacter
import OAI.Probability.CriticalPercolation.Modular.ActionUnimodularRoot

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

@[instance_reducible] def autEdgeAction : MulAction G.Aut E where
  smul φ e := φ.edge e
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

local instance : MulAction G.Aut E := G.autEdgeAction

lemma aut_preservesEnds : G.PreservesEnds (Λ := G.Aut) := fun φ => φ.preserves

lemma stabilizer_le_levelComponentGroup (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (o : V) (Q : Set ℝˣ) (v : V)
    (x : G.domainComponent (G.modularCoordinate hc hl o ⁻¹' Q) v) :
    MulAction.stabilizer G.Aut x.val ≤ componentKernel (G.modularUnitCharacter hc hl o)
      (G.domainComponent (G.modularCoordinate hc hl o ⁻¹' Q) v) := by
  intro φ hφ
  have hker := G.unit_stabilizer_le_kernel hc hl o x.val hφ
  change φ.vertex x.val = x.val at hφ
  refine ⟨hker,?_⟩
  have hS : ∀ y, φ.vertex y ∈ G.modularCoordinate hc hl o ⁻¹' Q ↔
      y ∈ G.modularCoordinate hc hl o ⁻¹' Q := by
    intro y
    change G.modularCoordinate hc hl o (φ • y) ∈ Q ↔ _
    rw [G.modularCoordinate_equivariant hc hl o φ y,hker,one_mul]
    rfl
  exact Aut.preserves_domainComponent G φ _ hS v x.val x.property
    (by rw [hφ]; exact x.property)

lemma levelComponent_suborbit_image (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (o : V) (Q : Set ℝˣ) (v : V) :
    let C := G.domainComponent (G.modularCoordinate hc hl o ⁻¹' Q) v
    let L := componentKernel (G.modularUnitCharacter hc hl o) C
    let _ := restrictedVertexAction C L (componentKernel_le _ _)
    ∀ x y : C, Subtype.val '' ActionOrbitTransport.stabilizerOrbit L C x y =
      G.stabilizerOrbit x.val y.val := by
  intro C L _ x y
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨φ,hx,hy⟩ := (ActionOrbitTransport.mem_stabilizerOrbit L C).mp hw
    exact G.mem_stabilizerOrbit.mpr ⟨φ.val,congrArg Subtype.val hx,congrArg Subtype.val hy⟩
  · intro hz
    obtain ⟨φ,hx,hy⟩ := G.mem_stabilizerOrbit.mp hz
    have hm : φ ∈ L := G.stabilizer_le_levelComponentGroup hc hl o Q v x hx
    let ψ : L := ⟨φ,hm⟩
    refine ⟨ψ • y,?_,hy⟩
    exact (ActionOrbitTransport.mem_stabilizerOrbit L C).mpr
      ⟨ψ,Subtype.ext hx,rfl⟩

lemma levelComponent_suborbit_finite (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (o : V) (Q : Set ℝˣ) (v : V) :
    let C := G.domainComponent (G.modularCoordinate hc hl o ⁻¹' Q) v
    let L := componentKernel (G.modularUnitCharacter hc hl o) C
    let _ := restrictedVertexAction C L (componentKernel_le _ _)
    ∀ x y : C, (ActionOrbitTransport.stabilizerOrbit L C x y).Finite := by
  intro C L _ x y
  apply Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
  rw [G.levelComponent_suborbit_image hc hl o Q v]
  exact G.stabilizerOrbit_finite hc hl x.val y.val

lemma levelComponent_suborbitCard (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (o : V) (Q : Set ℝˣ) (v : V) :
    let C := G.domainComponent (G.modularCoordinate hc hl o ⁻¹' Q) v
    let L := componentKernel (G.modularUnitCharacter hc hl o) C
    let _ := restrictedVertexAction C L (componentKernel_le _ _)
    ∀ x y : C, ActionOrbitTransport.suborbitCard L C x y = G.suborbitCard x.val y.val := by
  intro C L _ x y
  unfold ActionOrbitTransport.suborbitCard
  rw [←Set.ncard_image_of_injective _ Subtype.val_injective,
    G.levelComponent_suborbit_image hc hl o Q v]
  rfl

def levelComponent_unimodularRoot (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V)
    (Q : Set ℝˣ) (hQ : Q.Finite) (v : V) (hv : G.modularCoordinate hc hl o v ∈ Q) :
    (G.induce (G.domainComponent (G.modularCoordinate hc hl o ⁻¹' Q) v)).UnimodularRoot := Classical.choice (by
  let C := G.domainComponent (G.modularCoordinate hc hl o ⁻¹' Q) v
  let L := componentKernel (G.modularUnitCharacter hc hl o) C
  let := restrictedVertexAction C L (componentKernel_le _ _)
  let := G.restrictedEdgeAction G.aut_preservesEnds C L (componentKernel_le _ _)
  have ha := G.restricted_preservesEnds G.aut_preservesEnds C L (componentKernel_le _ _)
  obtain ⟨R,hR,hcover⟩ := hq
  have hcover' : ∀ x, ∃ u∈R, x∈MulAction.orbit G.Aut u := by
    intro x
    obtain ⟨u,hu,φ,hφ⟩ := hcover x
    exact ⟨u,hu,φ,hφ⟩
  obtain ⟨S,hS,hScover⟩ := G.componentKernel_finite_orbits G.aut_preservesEnds
    R hR hcover' (G.modularUnitCharacter hc hl o) (G.modularCoordinate hc hl o)
    (G.modularCoordinate_equivariant hc hl o) Q hQ v hv
  let w : C → ℝ := fun x => G.modularRatio o x.val
  have hw (φ : L) (x : C) : w (φ • x) = w x := by
    have hchar : G.modularUnitCharacter hc hl o φ.val = 1 := φ.property.1
    have hh := congrArg (fun u : ℝˣ => (u : ℝ))
      (G.modularCoordinate_equivariant hc hl o φ.val x.val)
    change G.modularRatio o (φ.val.vertex x.val) = _ at hh
    change G.modularRatio o (φ.val.vertex x.val) = _
    simpa only [hchar,one_mul,modularCoordinate_val] using hh
  have hb (x y : C) : w x * (ActionOrbitTransport.suborbitCard L C x y : ℝ) =
      w y * (ActionOrbitTransport.suborbitCard L C y x : ℝ) := by
    rw [G.levelComponent_suborbitCard hc hl o Q v,
      G.levelComponent_suborbitCard hc hl o Q v]
    exact G.modularRatio_card_balance hc hl o x.val y.val
  exact ⟨unimodularRoot_of_action (G.induce C) ha S hS hScover
    ⟨v,G.domainComponent_self _ _⟩ w (fun x => G.modularRatio_pos hc hl o x.val)
    hw (G.levelComponent_suborbit_finite hc hl o Q v) hb⟩)

end CriticalPercolation.BondGraph
end
end

end OAI
