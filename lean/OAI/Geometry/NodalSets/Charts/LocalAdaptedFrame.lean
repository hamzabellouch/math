import OAI.Geometry.NodalSets.Charts.AdaptedNormalChart
import OAI.Geometry.NodalSets.Charts.ContinuousAdaptedFrame

namespace OAI

namespace Yau.Geometry
open Filter
open scoped Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]

theorem exists_continuous_unit_adapted_frame (g : T → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hg : Continuous g) (hs : ∀ t u v, g t u v = g t v u)
    (p q : T → Coord) (hp : Continuous p) (hq : Continuous q)
    (hpp : ∀ t, g t (p t) (p t) = 1) (hqq : ∀ t, g t (q t) (q t) = 1)
    (hpq : ∀ t, g t (p t) (q t) = 0) (t0 : T)
    (hpos : ∀ v : Coord, v ≠ 0 → 0 < g t0 v v) :
    ∃ (U : Set T) (e : T → Fin 4 → Coord), U ∈ 𝓝 t0 ∧
      (∀ i, ContinuousOn (fun t ↦ e t i) U) ∧
      (∀ t, e t 0 = p t ∧ e t 1 = q t) ∧
      ∀ t ∈ U, ∀ i j, g t (e t i) (e t j) = if i = j then 1 else 0 := by
  obtain ⟨v, hv0, hv1, hv⟩ := positive_coordinate_adapted_frame (g t0) hpos (hs t0)
    (p t0) (q t0) 1 1 (by norm_num) (by norm_num)
    (by simpa using hpp t0) (by simpa using hqq t0) (hpq t0)
  exact continue_two_axes g hg hs p q hp hq hpp hqq hpq t0
    (fun i ↦ v (Pi.single i 1)) hv (by simpa using hv0) (by simpa using hv1)

theorem exists_continuous_adapted_frame (g : T → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hg : Continuous g) (hs : ∀ t u v, g t u v = g t v u)
    (hpos : ∀ t, ∀ v : Coord, v ≠ 0 → 0 < g t v v)
    (p q : T → Coord) (hp : Continuous p) (hq : Continuous q)
    (hp0 : ∀ t, p t ≠ 0) (hq0 : ∀ t, q t ≠ 0)
    (hpq : ∀ t, g t (p t) (q t) = 0) (t0 : T) :
    ∃ (U : Set T) (e : T → Fin 4 → Coord), U ∈ 𝓝 t0 ∧
      (∀ i, ContinuousOn (fun t ↦ e t i) U) ∧
      (∀ t, e t 0 = metricNormalize (g t) (p t) ∧ e t 1 = metricNormalize (g t) (q t)) ∧
      ∀ t ∈ U, ∀ i j, g t (e t i) (e t j) = if i = j then 1 else 0 := by
  apply exists_continuous_unit_adapted_frame g hg hs
    (fun t ↦ metricNormalize (g t) (p t)) (fun t ↦ metricNormalize (g t) (q t))
    (metricNormalize_continuous g p hg hp (fun t ↦ hpos t _ (hp0 t)))
    (metricNormalize_continuous g q hg hq (fun t ↦ hpos t _ (hq0 t)))
    (fun t ↦ metricNormalize_unit _ _ (hpos t _ (hp0 t)))
    (fun t ↦ metricNormalize_unit _ _ (hpos t _ (hq0 t)))
    _ t0 (hpos t0)
  intro t
  simp [metricNormalize, hpq]

end
end Yau.Geometry

end OAI
