import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.NormalOrbitAction
import OAI.Probability.CriticalPercolation.Classification.FaithfulOrbitalModel
import OAI.Probability.CriticalPercolation.Nilpotent.StructuredVirtuallyNilpotent
import OAI.Probability.CriticalPercolation.Criticality.SubexponentialVolumes

namespace OAI

section
noncomputable section
open Set Function MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

instance orbitalActionGroup_action (o : V) (L : ℕ) (Λ : Subgroup G.Aut) :
    MulAction (G.orbitalActionGroup o L Λ) (MulAction.orbit G.Aut o) where
  smul g u := g.val u
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def orbitalQuotientMap (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (H : Subgroup (G.orbitalActionGroup o L Λ)) [H.Normal] :
    Λ →* (G.orbitalActionGroup o L Λ) ⧸ H :=
  (QuotientGroup.mk' H).comp (G.orbitalActionMap o L Λ)

lemma orbitalQuotientMap_surjective (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (H : Subgroup (G.orbitalActionGroup o L Λ)) [H.Normal] :
    Surjective (G.orbitalQuotientMap o L Λ H) :=
  (QuotientGroup.mk'_surjective H).comp (G.orbitalActionMap_surjective o L Λ)

lemma orbitalQuotientMap_finite_kernel_orbits (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (H : Subgroup (G.orbitalActionGroup o L Λ)) [H.Normal]
    (hH : (MulAction.orbit H (⟨o,MulAction.mem_orbit_self o⟩ :
      MulAction.orbit G.Aut o)).Finite) :
    ∀ v : V, (MulAction.orbit (G.orbitalQuotientMap o L Λ H).ker v).Finite := by
  let _ : MulAction G.Aut E := G.autEdgeAction
  apply G.finite_kernel_orbits_from_one_vertex hc hl
    (G.subgroup_preservesEnds G.aut_preservesEnds Λ) (G.orbitalQuotientMap o L Λ H) o
  apply (hH.image Subtype.val).subset
  rintro v ⟨g,rfl⟩
  have hg : G.orbitalActionMap o L Λ g.val∈H :=
    (QuotientGroup.eq_one_iff _).mp g.property
  refine ⟨⟨g • o,?_⟩,?_,rfl⟩
  · exact ⟨g.val.val,rfl⟩
  · exact ⟨⟨G.orbitalActionMap o L Λ g.val,hg⟩,rfl⟩

def orbitalBlockProjection (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (H : Subgroup (G.orbitalActionGroup o L Λ)) (v : V) :
    NormalOrbit.Blocks (X := MulAction.orbit G.Aut o) H :=
  if h : v∈MulAction.orbit G.Aut o then NormalOrbit.block H ⟨v,h⟩
  else NormalOrbit.block H ⟨o,MulAction.mem_orbit_self o⟩

lemma orbitalBlockProjection_equivariant (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (H : Subgroup (G.orbitalActionGroup o L Λ)) [H.Normal]
    (g : Λ) :
    G.orbitalBlockProjection o L Λ H (g • o)=
      G.orbitalQuotientMap o L Λ H g • NormalOrbit.block H
        (⟨o,MulAction.mem_orbit_self o⟩ : MulAction.orbit G.Aut o) := by
  have hg : g • o∈MulAction.orbit G.Aut o := ⟨g.val,rfl⟩
  simp only [orbitalBlockProjection,dite_eq_left hg,orbitalQuotientMap,MonoidHom.comp_apply,
    NormalOrbit.mk_smul_block]
  rfl

lemma orbitalQuotientMap_finite_stabilizer_images (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (H : Subgroup (G.orbitalActionGroup o L Λ)) [H.Normal]
    (hstab : (MulAction.stabilizer ((G.orbitalActionGroup o L Λ) ⧸ H)
      (NormalOrbit.block H (⟨o,MulAction.mem_orbit_self o⟩ : MulAction.orbit G.Aut o)) :
      Set ((G.orbitalActionGroup o L Λ) ⧸ H)).Finite) :
    ∀ v : V, ((MulAction.stabilizer Λ v).map (G.orbitalQuotientMap o L Λ H) :
      Set ((G.orbitalActionGroup o L Λ) ⧸ H)).Finite := by
  let _ : MulAction G.Aut E := G.autEdgeAction
  exact G.finite_stabilizer_images_from_orbit_quotient hc hl
    (G.subgroup_preservesEnds G.aut_preservesEnds Λ) (G.orbitalQuotientMap o L Λ H)
    o (G.orbitalBlockProjection o L Λ H) _
    (G.orbitalBlockProjection_equivariant o L Λ H) hstab

theorem critical_null_of_orbital_nilpotent_quotient
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hg : G.SubexponentialGrowth)
    (o : V) (L : ℕ) (Λ : Subgroup G.Aut) [Group.FG Λ]
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (H : Subgroup (G.orbitalActionGroup o L Λ)) [H.Normal]
    (hH : (MulAction.orbit H (⟨o,MulAction.mem_orbit_self o⟩ :
      MulAction.orbit G.Aut o)).Finite)
    (hstab : (MulAction.stabilizer ((G.orbitalActionGroup o L Λ) ⧸ H)
      (NormalOrbit.block H (⟨o,MulAction.mem_orbit_self o⟩ : MulAction.orbit G.Aut o)) :
      Set ((G.orbitalActionGroup o L Λ) ⧸ H)).Finite)
    (N : Subgroup ((G.orbitalActionGroup o L Λ) ⧸ H)) [Group.IsNilpotent N]
    (hN : N.index≠0) (hpc : G.criticalProbability<1) :
    G.law G.criticalProbability G.percolates=0 := by
  let _ : MulAction G.Aut E := G.autEdgeAction
  exact G.critical_null_of_virtually_nilpotent_quotient hc hl hg
    (G.subgroup_preservesEnds G.aut_preservesEnds Λ) S hS hcover
    (G.orbitalQuotientMap o L Λ H) (G.orbitalQuotientMap_surjective o L Λ H)
    (G.orbitalQuotientMap_finite_kernel_orbits hc hl o L Λ H hH)
    (G.orbitalQuotientMap_finite_stabilizer_images hc hl o L Λ H hstab) N hN hpc

end CriticalPercolation.BondGraph
end
end

end OAI
