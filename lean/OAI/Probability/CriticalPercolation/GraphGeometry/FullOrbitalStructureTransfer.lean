import Mathlib
import OAI.Probability.CriticalPercolation.GraphTopology.GraphNeighborhoodCompact
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.GraphGeometry.OrbitalAction
import OAI.Probability.CriticalPercolation.GraphGeometry.OrbitQuotientTransfer
import OAI.Probability.CriticalPercolation.Modular.ModularLevelGeometry
import OAI.Probability.CriticalPercolation.Nilpotent.StructuredVirtuallyNilpotent

namespace OAI

section
noncomputable section
open Set Function MeasureTheory Topology
open scoped Classical ENNReal

namespace CriticalPercolation
namespace StructurePullback
variable {A B : Type*} [Group A] [Group B]

lemma nilpotent_comap_of_injective (f : A →* B) (hf : Injective f)
    (N : Subgroup B) [Group.IsNilpotent N] : Group.IsNilpotent (N.comap f) := by
  let F : N.comap f →* N :=
    {toFun := fun g => ⟨f g.val,g.property⟩
     map_one' := Subtype.ext (map_one f)
     map_mul' := fun g h => Subtype.ext (map_mul f g.val h.val)}
  have hF : Injective F := by
    intro g h he
    apply Subtype.ext
    exact hf (congrArg Subtype.val he)
  apply Subgroup.isNilpotent_of_ker_le_center F
  rw [(MonoidHom.ker_eq_bot_iff F).mpr hF]
  exact bot_le

lemma finiteIndex_comap (f : A →* B) (N : Subgroup B) (hN : N.index≠0) :
    (N.comap f).index≠0 := by
  rw [Subgroup.index_comap]
  intro h
  exact hN (Subgroup.index_eq_zero_of_relIndex_eq_zero h)

end StructurePullback
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma finite_stabilizer_images_from_one_vertex
    {A B : Type*} [Group A] [Group B] [MulAction A V] [MulAction A E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ha : G.PreservesEnds (Λ := A)) (ρ : A →* B) (o : V)
    (ho : ((MulAction.stabilizer A o).map ρ : Set B).Finite) :
    ∀ v : V, ((MulAction.stabilizer A v).map ρ : Set B).Finite := by
  let a : V → A := fun w => if h : ∃ g : A, g • o=w then h.choose else 1
  have ha' : ∀ {w : V}, (∃ g : A, g • o=w) → a w • o=w := by
    intro w hw
    simp only [a, dite_eq_left hw]
    exact hw.choose_spec
  intro v
  obtain ⟨n,hn⟩ := G.reachable_mem_vertexBall (hc v o)
  apply ((G.vertexBall_finite hl v n).biUnion
    (fun w _ => ho.image (fun b => ρ (a w)*b))).subset
  rintro b ⟨g,hg,rfl⟩
  have hgo : g • o∈G.vertexBall v n := by
    have hh := (Aut.vertexBall_mem G (G.smulAut ha g) v o n).mpr hn
    change g • o∈G.vertexBall (g • v) n at hh
    exact hg ▸ hh
  refine Set.mem_iUnion₂.mpr ⟨g • o,hgo,ρ ((a (g • o))⁻¹*g),?_,?_⟩
  · refine ⟨(a (g • o))⁻¹*g,?_,rfl⟩
    change ((a (g • o))⁻¹*g) • o=o
    rw [mul_smul]
    calc
      (a (g • o))⁻¹ • (g • o) = (a (g • o))⁻¹ • (a (g • o) • o) :=
        congrArg (fun x => (a (g • o))⁻¹ • x) (ha' ⟨g,rfl⟩).symm
      _ = o := inv_smul_smul _ _
  · simp only [map_mul, map_inv, mul_inv_cancel_left]

def fullOrbitalQuotientHom (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (H : Subgroup (G.orbitPower o L ≃g G.orbitPower o L)) [H.Normal] :
    Λ →* (G.orbitPower o L ≃g G.orbitPower o L) ⧸ H :=
  (QuotientGroup.mk' H).comp ((G.orbitPowerHom o L).comp Λ.subtype)

lemma fullOrbital_finite_kernel_orbits (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (H : Subgroup (G.orbitPower o L ≃g G.orbitPower o L)) [H.Normal]
    (hH : ((fun g : G.orbitPower o L ≃g G.orbitPower o L =>
      g (⟨o,MulAction.mem_orbit_self o⟩ : MulAction.orbit G.Aut o)) '' (H : Set _)).Finite) :
    ∀ v : V, (MulAction.orbit (G.fullOrbitalQuotientHom o L Λ H).rangeRestrict.ker v).Finite := by
  let _ : MulAction G.Aut E := G.autEdgeAction
  apply G.finite_kernel_orbits_from_one_vertex hc hl
    (G.subgroup_preservesEnds G.aut_preservesEnds Λ) _ o
  apply (hH.image Subtype.val).subset
  rintro v ⟨g,rfl⟩
  have he := congrArg Subtype.val g.property
  have hg : G.orbitPowerHom o L g.val.val∈H := (QuotientGroup.eq_one_iff _).mp he
  exact ⟨⟨g • o,⟨g.val.val,rfl⟩⟩,⟨G.orbitPowerHom o L g.val.val,hg,rfl⟩,rfl⟩

lemma fullOrbital_finite_stabilizer_images (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (H : Subgroup (G.orbitPower o L ≃g G.orbitPower o L)) [H.Normal]
    (hstab : (((QuotientGroup.mk' H) : (G.orbitPower o L ≃g G.orbitPower o L) → _)
      '' {g | g (⟨o,MulAction.mem_orbit_self o⟩ : MulAction.orbit G.Aut o)=
        ⟨o,MulAction.mem_orbit_self o⟩}).Finite) :
    ∀ v : V, ((MulAction.stabilizer Λ v).map
      (G.fullOrbitalQuotientHom o L Λ H).rangeRestrict :
      Set (G.fullOrbitalQuotientHom o L Λ H).range).Finite := by
  let _ : MulAction G.Aut E := G.autEdgeAction
  apply G.finite_stabilizer_images_from_one_vertex hc hl
    (G.subgroup_preservesEnds G.aut_preservesEnds Λ) _ o
  apply (hstab.preimage Subtype.val_injective.injOn).subset
  rintro g ⟨a,ha,rfl⟩
  refine ⟨G.orbitPowerHom o L a.val,?_,rfl⟩
  apply Subtype.ext
  exact ha

theorem critical_null_of_compact_open_orbital_quotient
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hg : G.SubexponentialGrowth)
    (o : V) (L : ℕ) (hconn : (G.orbitPower o L).Connected)
    (Λ : Subgroup G.Aut) [Group.FG Λ]
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (H : Subgroup (G.orbitPower o L ≃g G.orbitPower o L)) [H.Normal]
    (N : Subgroup ((G.orbitPower o L ≃g G.orbitPower o L) ⧸ H)) [Group.IsNilpotent N]
    (hN : N.index≠0)
    (hH : let _ : TopologicalSpace (MulAction.orbit G.Aut o) := ⊥
      let _ : TopologicalSpace (G.orbitPower o L ≃g G.orbitPower o L) :=
        GraphTopology.autTopology (G.orbitPower o L)
      IsCompact (H : Set (G.orbitPower o L ≃g G.orbitPower o L)) ∧
      IsOpen (H : Set (G.orbitPower o L ≃g G.orbitPower o L)))
    (hpc : G.criticalProbability<1) : G.law G.criticalProbability G.percolates=0 := by
  let _ : TopologicalSpace (MulAction.orbit G.Aut o) := ⊥
  let _ : DiscreteTopology (MulAction.orbit G.Aut o) := ⟨rfl⟩
  let _ : TopologicalSpace (G.orbitPower o L ≃g G.orbitPower o L) :=
    GraphTopology.autTopology (G.orbitPower o L)
  let _ : DiscreteTopology ((G.orbitPower o L ≃g G.orbitPower o L) ⧸ H) :=
    QuotientGroup.discreteTopology hH.2
  let o' : MulAction.orbit G.Aut o := ⟨o,MulAction.mem_orbit_self o⟩
  have hstab : (((QuotientGroup.mk' H) : (G.orbitPower o L ≃g G.orbitPower o L) → _)
      '' {g | g o'=o'}).Finite := by
    apply isCompact_iff_finite.mp
    apply (GraphTopology.compact_stabilizer (G.orbitPower o L) hconn
      (G.powerOn_finite_neighbors hl _ _) o').image
    exact QuotientGroup.continuous_mk
  let f := G.fullOrbitalQuotientHom o L Λ H
  let M := N.comap f.range.subtype
  let _ : Group.IsNilpotent M := StructurePullback.nilpotent_comap_of_injective
    f.range.subtype Subtype.val_injective N
  let _ : MulAction G.Aut E := G.autEdgeAction
  exact G.critical_null_of_virtually_nilpotent_quotient hc hl hg
    (G.subgroup_preservesEnds G.aut_preservesEnds Λ) S hS hcover
    f.rangeRestrict (MonoidHom.rangeRestrict_surjective f)
    (G.fullOrbital_finite_kernel_orbits hc hl o L Λ H
      (GraphTopology.compact_finite_vertex_images _ _ hH.1 o'))
    (G.fullOrbital_finite_stabilizer_images hc hl o L Λ H hstab) M
    (StructurePullback.finiteIndex_comap f.range.subtype N hN) hpc

end BondGraph
end CriticalPercolation
end
end

end OAI
