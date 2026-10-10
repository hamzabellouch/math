import OAI.Geometry.NodalSets.Charts.LocalAdaptedFrame

namespace OAI

namespace Yau.Geometry
open Filter
open scoped Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]

lemma metricNormalize_rescale (g : Coord →L[ℝ] Coord →L[ℝ] ℝ) (v : Coord)
    (h : 0 < g v v) : Real.sqrt (g v v) • metricNormalize g v = v := by
  simp [metricNormalize, smul_smul, ne_of_gt (Real.sqrt_pos.mpr h)]

theorem continue_admissible_direction (g H : T → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hg : Continuous g) (hH : Continuous H)
    (hpos : ∀ t, ∀ v : Coord, v ≠ 0 → 0 < g t v v)
    (p : T → Coord) (hp : Continuous p) (hp0 : ∀ t, p t ≠ 0)
    (t0 : T) (q0 : Coord) (hperp : g t0 (p t0) q0 = 0)
    (hlen : g t0 q0 q0 = g t0 (p t0) (p t0)+4)
    (hstrict : 0 < H t0 (p t0) (p t0)+H t0 q0 q0) :
    ∃ (U : Set T) (q : T → Coord), U ∈ 𝓝 t0 ∧ ContinuousOn q U ∧ q t0 = q0 ∧
      ∀ t ∈ U, g t (p t) (q t) = 0 ∧
        g t (q t) (q t) = g t (p t) (p t)+4 ∧
        0 < H t (p t) (p t)+H t (q t) (q t) := by
  let e := fun t ↦ metricNormalize (g t) (p t)
  have he : Continuous e := metricNormalize_continuous g p hg hp (fun t ↦ hpos t _ (hp0 t))
  let a : T → Fin 1 → Coord := fun t _ ↦ e t
  have ha (t : T) (i j : Fin 1) : g t (a t i) (a t j) = if i = j then 1 else 0 := by
    have hij : i = j := Subsingleton.elim _ _
    simpa [a, hij] using metricNormalize_unit (g t) (p t) (hpos t _ (hp0 t))
  let z := fun t ↦ removeFrame (g t) (a t) q0
  have hz : Continuous z := removeFrame_continuous g a (fun _ ↦ q0) hg (fun _ ↦ he) continuous_const
  have hz0 : z t0 = q0 := by
    apply removeFrame_fixed
    intro i
    simp [a, e, metricNormalize, hperp]
  have hl (t : T) : 0 < g t (p t) (p t)+4 := by have hh := hpos t _ (hp0 t); linarith
  have hzpos : 0 < g t0 (z t0) (z t0) := by rw [hz0, hlen]; exact hl t0
  let q := fun t ↦ Real.sqrt (g t (p t) (p t)+4) • metricNormalize (g t) (z t)
  have hqc {t : T} (ht : 0 < g t (z t) (z t)) : ContinuousAt q t :=
    (((hg.continuousAt.clm_apply hp.continuousAt).clm_apply hp.continuousAt).add continuousAt_const).sqrt.smul
      (metricNormalize_continuousAt g z hg.continuousAt hz.continuousAt ht)
  have hq0 : q t0 = q0 := by
    dsimp [q]
    rw [hz0, ← hlen]
    exact metricNormalize_rescale _ _ (by rw [hlen]; exact hl t0)
  let U : Set T := {t | 0 < g t (z t) (z t)} ∩
    {t | 0 < H t (p t) (p t)+H t (q t) (q t)}
  have hU : U ∈ 𝓝 t0 := by
    apply inter_mem
    · exact (isOpen_lt continuous_const ((hg.clm_apply hz).clm_apply hz)).mem_nhds hzpos
    · have hc := ((hH.continuousAt.clm_apply hp.continuousAt).clm_apply hp.continuousAt).add
        ((hH.continuousAt.clm_apply (hqc hzpos)).clm_apply (hqc hzpos))
      exact hc.preimage_mem_nhds (Ioi_mem_nhds (by simpa [hq0] using hstrict))
  refine ⟨U, q, hU, fun t ht ↦ (hqc ht.1).continuousWithinAt, hq0, ?_⟩
  intro t ht
  refine ⟨?_, ?_, ht.2⟩
  · have hzorth : g t (e t) (z t) = 0 := removeFrame_orthogonal (g t) (a t) (ha t) q0 0
    have hpz : g t (p t) (z t) = 0 := by
      rw [← metricNormalize_rescale (g t) (p t) (hpos t _ (hp0 t))]
      simp only [map_smul, smul_apply, smul_eq_mul]
      change Real.sqrt (g t (p t) (p t)) * g t (e t) (z t) = 0
      rw [hzorth, mul_zero]
    simp [q, metricNormalize, hpz]
  · have hu := metricNormalize_unit (g t) (z t) ht.1
    dsimp [q]
    simp only [map_smul, smul_apply, smul_eq_mul, hu, mul_one]
    nlinarith [Real.sq_sqrt (hl t).le]

end
end Yau.Geometry

end OAI
