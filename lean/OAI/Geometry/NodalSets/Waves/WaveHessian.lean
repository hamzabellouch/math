import OAI.Geometry.NodalSets.Waves.WaveSecondJet

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma sourceHessian_symmetric_at
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (f : Coord → ℝ) (x : Coord) (hf : ContDiffAt ℝ ∞ f x) (u v : Coord) :
    sourceHessian g f x u v = sourceHessian g f x v u := by
  simp only [sourceHessian_apply]
  rw [hf.isSymmSndFDerivAt
    (by simp) u v,
    actual_connection_symmetric g hg hs hp x u v]

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {y : T → Coord} {d : SourceFrameTriple g S y} {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

omit [CompactSpace T] in
theorem phase_hessian
    (hg : ContDiff ℝ ∞ g) (hs : ∀ x u v, g x u v = g x v u)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hS : ContDiff ℝ ∞ S)
    (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) (t : T × Fin 3) (u v : Coord) :
    sourceHessian g (fun z ↦ (b.phase t z).re) (y t.1) u v =
      sourceHessian g S (y t.1) u v -
        sourceDirectionEta (g (y t.1)) (sourceHessian g S (y t.1))
          (metricGradient g S (y t.1)) (d.q t.1 t.2) * g (y t.1) u v := by
  have hu := b.phase_second hg hs hp hS hp0 t u
  have hv := b.phase_second hg hs hp hS hp0 t v
  have huv := b.phase_second hg hs hp hS hp0 t (u+v)
  have hsym := sourceHessian_symmetric_at g hg hs hp (fun z ↦ (b.phase t z).re) (y t.1)
    (Complex.reCLM.contDiff.contDiffAt.comp _ (b.phase_smooth_at_center t)) v u
  have hSsym := sourceHessian_symmetric_at g hg hs hp S (y t.1) hS.contDiffAt v u
  simp only [map_add,add_apply] at huv
  rw [hsym,hSsym,hs (y t.1) v u] at huv
  nlinarith

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
