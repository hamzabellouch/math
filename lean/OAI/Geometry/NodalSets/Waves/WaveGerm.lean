import OAI.Geometry.NodalSets.Waves.WaveCenterJets

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T]
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {y : T → Coord} {d : SourceFrameTriple g S y} {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

lemma wave_germ (N : ℝ) (hN : 0 < N) (t : T × Fin 3) :
    b.wave N t =ᶠ[𝓝 (y t.1)]
      (fun x ↦ b.amplitude N t x * Complex.exp ((N:ℂ)*b.phase t x)) := by
  have hcut : Yau.Waves.scaledCutoff N (0:Coord) =ᶠ[𝓝 (0:Coord)] (fun _ ↦ 1) := by
    filter_upwards [Metric.ball_mem_nhds (0:Coord) (Real.rpow_pos_of_pos hN (-1/3:ℝ))] with z hz
    exact Yau.Waves.scaledCutoff_eq_one hN 0 z (by simpa only [Metric.mem_ball,dist_eq_norm] using hz.le)
  have hInv : Tendsto ((b.F t).symm : Coord → Coord) (𝓝 (y t.1)) (𝓝 0) := by
    have hh := (b.inverse_derivative t).continuousAt
    simpa only [ContinuousAt,b.inverse_center] using hh
  filter_upwards [chartPushforward_eventually (b.F t) (coordinateWave b.phi b.A J N t)
    (y t.1) (b.center_mem_target t),hcut.comp_tendsto hInv] with z hz hc
  change chartPushforward (b.F t) (coordinateWave b.phi b.A J N t) z = _
  rw [hz]
  change Yau.Waves.scaledCutoff N 0 ((b.F t).symm z) • _ = _
  change Yau.Waves.scaledCutoff N 0 ((b.F t).symm z) = 1 at hc
  rw [hc,one_smul]
  rfl

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
