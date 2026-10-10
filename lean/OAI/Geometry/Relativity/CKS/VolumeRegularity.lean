import OAI.Geometry.Relativity.CKS.VolumeDefinitions

namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSIntrinsicVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

lemma chartFrame_eq_symmL (x : M) {y : E}
    (hy : y ∈ (extChartAt I x).target) :
    chartFrame x y = (trivializationAt E (TangentSpace I) x).symmL ℝ
      ((extChartAt I x).symm y) := by
  have hs : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    simpa using (extChartAt I x).map_target hy
  rw [TangentBundle.symmL_trivializationAt hs, (extChartAt I x).right_inv hy]
  rfl

lemma chartFrame_continuousOn (x : M) (v : E) :
    ContinuousOn (fun y => (⟨(extChartAt I x).symm y, chartFrame x y v⟩ :
      TotalSpace E (TangentSpace I))) (extChartAt I x).target := by
  let e := trivializationAt E (TangentSpace I) x
  have h : ContinuousOn (fun y =>
      (⟨(extChartAt I x).symm y, e.symm ((extChartAt I x).symm y) v⟩ :
      TotalSpace E (TangentSpace I))) (extChartAt I x).target :=
    e.continuousOn_symm.comp
      ((continuousOn_extChartAt_symm x).prodMk continuousOn_const)
      (fun y hy => ⟨by simpa [e] using (extChartAt I x).map_target hy, mem_univ _⟩)
  apply h.congr
  intro y hy
  dsimp only
  congr 1
  rw [chartFrame_eq_symmL x hy, Trivialization.symmL_apply]
  simpa using (extChartAt I x).map_target hy

lemma chartMatrix_continuousOn (g : Metric (M := M)) (x : M) :
    ContinuousOn (chartMatrix g x) (extChartAt I x).target := by
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  apply continuousOn_pi.2
  intro i
  apply continuousOn_pi.2
  intro j
  exact (chartFrame_continuousOn x (basis i)).inner_bundle
    (chartFrame_continuousOn x (basis j))

lemma chartDensity_continuousOn (g : Metric (M := M)) (x : M) :
    ContinuousOn (chartDensity g x) (extChartAt I x).target := by
  exact ((continuous_id.matrix_det : Continuous (Matrix.det : Matrix (Fin 3) (Fin 3) ℝ → ℝ)).comp_continuousOn (chartMatrix_continuousOn g x)).sqrt

end CKSIntrinsicVolume

end

end OAI
