import OAI.Geometry.NodalSets.Charts.LocalFrameTriple

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T]
variable {g H : T → Coord →L[ℝ] Coord →L[ℝ] ℝ} {p : T → Coord}
namespace AdmissibleFrameTriple
variable (d : AdmissibleFrameTriple g H p)
def frame (z : T × Fin 3) : Coord ≃L[ℝ] Coord :=
  frameEquiv (g z.1) (d.e z.1 z.2) (d.orthonormal z.1 z.2)
def alpha (t : T) : ℝ := Real.sqrt (g t (p t) (p t))
def beta (t : T) : ℝ := Real.sqrt (g t (p t) (p t)+4)

lemma continuous_frame : Continuous (fun z ↦ (d.frame z).toContinuousLinearMap) := by
  apply continuous_prod_of_discrete_right.mpr
  intro j
  exact frameEquiv_continuous g (fun t ↦ d.e t j) (d.continuous_e j) (fun t ↦ d.orthonormal t j)

lemma frame_orthonormal (z : T × Fin 3) (i j : Fin 4) :
    g z.1 (d.frame z (Pi.single i 1)) (d.frame z (Pi.single j 1)) = if i=j then 1 else 0 := by
  change g z.1 (frameMap (d.e z.1 z.2) (Pi.single i 1))
    (frameMap (d.e z.1 z.2) (Pi.single j 1)) = _
  simp only [frameMap_axis,d.orthonormal]

lemma frame_first (hpos : ∀ t v, v ≠ 0 → 0 < g t v v) (hp0 : ∀ t, p t ≠ 0)
    (z : T × Fin 3) : alpha (g := g) (p := p) z.1 • d.frame z (Pi.single 0 1) = p z.1 := by
  change alpha z.1 • frameMap (d.e z.1 z.2) (Pi.single 0 1) = _
  rw [frameMap_axis,d.first]
  simp [alpha,metricNormalize,smul_smul,ne_of_gt (Real.sqrt_pos.mpr (hpos z.1 _ (hp0 z.1)))]

lemma frame_second (hpos : ∀ t v, v ≠ 0 → 0 < g t v v) (hp0 : ∀ t, p t ≠ 0)
    (z : T × Fin 3) : beta (g := g) (p := p) z.1 • d.frame z (Pi.single 1 1) = d.q z.1 z.2 := by
  have hb : 0 < g z.1 (p z.1) (p z.1)+4 := by have h := hpos z.1 _ (hp0 z.1); linarith
  change beta z.1 • frameMap (d.e z.1 z.2) (Pi.single 1 1) = _
  rw [frameMap_axis,d.second]
  simp [beta,metricNormalize,d.length,smul_smul,ne_of_gt (Real.sqrt_pos.mpr hb)]
end AdmissibleFrameTriple

end
end Yau.Geometry

end OAI
