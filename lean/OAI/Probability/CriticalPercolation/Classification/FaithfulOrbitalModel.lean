import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteIndexAction
import OAI.Probability.CriticalPercolation.GraphGeometry.OrbitQuotientTransfer
import OAI.Probability.CriticalPercolation.GraphGeometry.OrbitalFiniteGeneration
import OAI.Probability.CriticalPercolation.GraphGeometry.OrbitalScales
import OAI.Probability.CriticalPercolation.Modular.ModularLevelGeometry

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def orbitalActionGroup (o : V) (L : ℕ) (Λ : Subgroup G.Aut) :
    Subgroup (G.orbitPower o L ≃g G.orbitPower o L) :=
  ((G.orbitPowerHom o L).comp Λ.subtype).range

def orbitalActionMap (o : V) (L : ℕ) (Λ : Subgroup G.Aut) :
    Λ →* G.orbitalActionGroup o L Λ :=
  ((G.orbitPowerHom o L).comp Λ.subtype).rangeRestrict

lemma orbitalActionMap_surjective (o : V) (L : ℕ) (Λ : Subgroup G.Aut) :
    Surjective (G.orbitalActionMap o L Λ) := MonoidHom.rangeRestrict_surjective _

instance orbitalActionGroup_fg (o : V) (L : ℕ) (Λ : Subgroup G.Aut) [Group.FG Λ] :
    Group.FG (G.orbitalActionGroup o L Λ) :=
  Group.fg_of_surjective (G.orbitalActionMap_surjective o L Λ)

lemma orbitalActionMap_kernel_fixes (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (φ : (G.orbitalActionMap o L Λ).ker) : φ • o=o := by
  have hh := congrArg Subtype.val φ.property
  change (G.orbitPowerHom o L φ.val.val) = 1 at hh
  let o' : MulAction.orbit G.Aut o := ⟨o,MulAction.mem_orbit_self o⟩
  have ho := congrArg (fun f : G.orbitPower o L ≃g G.orbitPower o L => (f o').val) hh
  exact ho

lemma orbitalActionMap_finite_kernel_orbits (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (o : V) (L : ℕ) (Λ : Subgroup G.Aut) :
    ∀ v : V, (MulAction.orbit (G.orbitalActionMap o L Λ).ker v).Finite := by
  let _ : MulAction G.Aut E := G.autEdgeAction
  apply G.finite_kernel_orbits_from_one_vertex hc hl
    (G.subgroup_preservesEnds G.aut_preservesEnds Λ) (G.orbitalActionMap o L Λ) o
  apply (Set.finite_singleton o).subset
  rintro v ⟨φ,rfl⟩
  exact G.orbitalActionMap_kernel_fixes o L Λ φ

lemma orbitalActionGroup_transitive (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (horbit : MulAction.orbit Λ o=MulAction.orbit G.Aut o)
    (u v : MulAction.orbit G.Aut o) :
    ∃ φ : G.orbitalActionGroup o L Λ, φ.val u=v := by
  have hu : u.val∈MulAction.orbit Λ o := by rw [horbit]; exact u.property
  have hv : v.val∈MulAction.orbit Λ o := by rw [horbit]; exact v.property
  obtain ⟨a,ha⟩ := hu
  obtain ⟨b,hb⟩ := hv
  refine ⟨G.orbitalActionMap o L Λ (b*a⁻¹),?_⟩
  apply Subtype.ext
  change (b*a⁻¹) • u.val=v.val
  change a • o=u.val at ha
  change b • o=v.val at hb
  rw [←ha,mul_smul,inv_smul_smul,hb]

theorem sparse_polynomial_faithful_orbital_model [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (o : V) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d) :
    ∃ C : ℕ, ∃ Λ : Subgroup G.Aut, Group.FG Λ ∧
      (G.orbitPower o (2*C+1)).Connected ∧
      (MulAction.orbit G.Aut o).Infinite ∧
      (∀ u, ((G.orbitPower o (2*C+1)).neighborSet u).Finite) ∧
      (∀ u v, ∃ φ : G.orbitalActionGroup o (2*C+1) Λ, φ.val u=v) ∧
      (∀ v : V, (MulAction.orbit (G.orbitalActionMap o (2*C+1) Λ).ker v).Finite) ∧
      (∃ S : Set V, S.Finite ∧ ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) ∧
      (∀ R : ℕ, ∃ n≥R, ∀ u : MulAction.orbit G.Aut o,
        {v | ∃ p : (G.orbitPower o (2*C+1)).Walk u v, p.length≤n}.ncard≤n^(d+1)) := by
  obtain ⟨C,hC,hdense,hscales⟩ := G.orbital_power_polynomial_scales hc hl hq o d hpoly
  obtain ⟨Λ,hΛ,horbit,hreps⟩ := G.finitelyGenerated_quasiTransitive_subgroup hc hl hq o
  refine ⟨C,Λ,hΛ,hC,G.dense_set_infinite hl hdense,?_,?_,?_,hreps,hscales⟩
  · exact G.powerOn_finite_neighbors hl _ _
  · exact G.orbitalActionGroup_transitive o (2*C+1) Λ horbit
  · exact G.orbitalActionMap_finite_kernel_orbits hc hl o (2*C+1) Λ

end CriticalPercolation.BondGraph
end
end

end OAI
