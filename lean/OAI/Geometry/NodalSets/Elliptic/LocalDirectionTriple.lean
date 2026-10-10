import Mathlib.Analysis.Normed.Module.FiniteDimension
import OAI.Geometry.NodalSets.Elliptic.AdmissibleDirectionTriple

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]

theorem continue_admissible_triple (g H : T → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hg : Continuous g) (hH : Continuous H)
    (hpos : ∀ t, ∀ v : Coord, v ≠ 0 → 0 < g t v v)
    (p : T → Coord) (hp : Continuous p) (hp0 : ∀ t, p t ≠ 0)
    (t0 : T) (q0 : Fin 3 → Coord) (hInd : LinearIndependent ℝ q0)
    (hperp : ∀ j, g t0 (p t0) (q0 j) = 0)
    (hlen : ∀ j, g t0 (q0 j) (q0 j) = g t0 (p t0) (p t0)+4)
    (hstrict : ∀ j, 0 < H t0 (p t0) (p t0)+H t0 (q0 j) (q0 j)) :
    ∃ (U : Set T) (q : T → Fin 3 → Coord), U ∈ 𝓝 t0 ∧ ContinuousOn q U ∧ q t0 = q0 ∧
      ∀ t ∈ U, LinearIndependent ℝ (q t) ∧ ∀ j,
        g t (p t) (q t j) = 0 ∧ g t (q t j) (q t j) = g t (p t) (p t)+4 ∧
          0 < H t (p t) (p t)+H t (q t j) (q t j) := by
  have hex (j : Fin 3) := continue_admissible_direction g H hg hH hpos p hp hp0
    t0 (q0 j) (hperp j) (hlen j) (hstrict j)
  choose Uj qj hUj hqj hq0 hprop using hex
  let q : T → Fin 3 → Coord := fun t j ↦ qj j t
  have hqt : q t0 = q0 := funext hq0
  have hqc : ContinuousAt q t0 := continuousAt_pi.mpr (fun j ↦ (hqj j).continuousAt (hUj j))
  have hI : ∀ᶠ t in 𝓝 t0, LinearIndependent ℝ (q t) := by
    have hh : ∀ᶠ q' : Fin 3 → Coord in 𝓝 (q t0), LinearIndependent ℝ q' := by
      rw [hqt]
      exact hInd.eventually
    exact hqc.eventually hh
  let U : Set T := {t | LinearIndependent ℝ (q t)} ∩ ⋂ j, Uj j
  have hU : U ∈ 𝓝 t0 := inter_mem hI (Filter.iInter_mem.mpr hUj)
  refine ⟨U,q,hU,?_,hqt,?_⟩
  · apply continuousOn_pi.mpr
    intro j
    exact (hqj j).mono (fun t ht ↦ mem_iInter.mp ht.2 j)
  · intro t ht
    exact ⟨ht.1,fun j ↦ hprop j t (mem_iInter.mp ht.2 j)⟩

end
end Yau.Geometry

end OAI
