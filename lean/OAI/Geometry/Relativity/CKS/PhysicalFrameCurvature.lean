import OAI.Geometry.Relativity.CKS.PhysicalFrameConnection

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology

 def frameConnectionField (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : CKSFrame.ConnectionData :=
  CKSFrame.extractConnection (frameCoefficient G E x)

 def connectionFieldDerivative (c : PhysicalPoint → CKSFrame.ConnectionData)
    (e x : PhysicalPoint) : CKSFrame.ConnectionData where
  B := fun a => D e (fun y => (c y).B a) x
  rotation := D e (fun y => (c y).rotation) x
  chi11 := D e (fun y => (c y).chi11) x
  chi12 := D e (fun y => (c y).chi12) x
  chi22 := D e (fun y => (c y).chi22) x
  leaf := fun a => D e (fun y => (c y).leaf a) x

lemma connectionFieldDerivative_exact (c : PhysicalPoint → CKSFrame.ConnectionData)
    (e x : PhysicalPoint) (i j k : Fin 3) :
    CKSFrame.connection (connectionFieldDerivative c e x) i j k =
      D e (fun y => CKSFrame.connection (c y) i j k) x := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [connectionFieldDerivative,CKSFrame.connection,D,fderiv_fun_neg]

 def ActualAdaptedAt (G : PhysicalPoint → AmbientMat) (E : LocalFrame) (x : PhysicalPoint) : Prop :=
  DifferentiableAt ℝ G x ∧ (∀ i, DifferentiableAt ℝ (E i) x) ∧ (G x).PosDef ∧
  (∀ᶠ y in 𝓝 x, (G y).IsHermitian) ∧
  (∀ᶠ y in 𝓝 x, ∀ i j, metricPair (G y) (E i y) (E j y) = if i=j then 1 else 0) ∧
  (∀ a b : Fin 2, frameBracketCoefficient G E x a.succ b.succ 0=0)

lemma frame_connection_actual {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (h : ActualAdaptedAt G E x) :
    CKSFrame.connection (frameConnectionField G E x)=frameCoefficient G E x := by
  obtain ⟨hg,he,hp,hs,ho,ht⟩ := h
  apply CKSFrame.extractConnection_complete (frameCoefficient_metric hg he hp hs ho)
  have h1 := frameCoefficient_torsion (E := E) hs 1 2 0
  have hm1 := frameCoefficient_metric hg he hp hs ho 1 2 0
  have hm2 := frameCoefficient_metric hg he hp hs ho 2 1 0
  have hh := ht 0 1
  change frameBracketCoefficient G E x 1 2 0=0 at hh
  rw [hh] at h1
  linarith

 def actualFrameCurvature (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (i j k l : Fin 3) : ℝ :=
  D (E i x) (fun y => frameCoefficient G E y j k l) x -
  D (E j x) (fun y => frameCoefficient G E y i k l) x +
  ∑ m, (frameCoefficient G E x j k m*frameCoefficient G E x i m l -
    frameCoefficient G E x i k m*frameCoefficient G E x j m l -
    frameBracketCoefficient G E x i j m*frameCoefficient G E x m k l)

 def actualFrameScalar (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : ℝ := ∑ i, ∑ j, actualFrameCurvature G E x i j j i

lemma physical_curvature_representation {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (h : ∀ᶠ y in 𝓝 x, ActualAdaptedAt G E y)
    (i j k l : Fin 3) :
    actualFrameCurvature G E x i j k l = CKSFrame.curvature
      (frameConnectionField G E x)
      (fun a => connectionFieldDerivative (frameConnectionField G E) (E a x) x) i j k l := by
  have hx := h.self_of_nhds
  have hc := frame_connection_actual hx
  have hd (a b d f : Fin 3) :
      D (E a x) (fun y => frameCoefficient G E y b d f) x =
      D (E a x) (fun y => CKSFrame.connection (frameConnectionField G E y) b d f) x := by
    apply D_congr
    filter_upwards [h] with y hy
    rw [frame_connection_actual hy]
  unfold actualFrameCurvature CKSFrame.curvature
  simp_rw [connectionFieldDerivative_exact, hc]
  simp_rw [← hd]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [frameCoefficient_torsion hx.2.2.2.1]

theorem physical_scalar_decomposition {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (h : ∀ᶠ y in 𝓝 x, ActualAdaptedAt G E y) :
    let c := frameConnectionField G E x
    let dc := fun a => connectionFieldDerivative (frameConnectionField G E) (E a x) x
    actualFrameScalar G E x = CKSFrame.leafScalar c dc - 2*CKSFrame.normalMean dc -
      (CKSFrame.mean c)^2-CKSFrame.chiNormSq c+2*CKSFrame.accelDiv c dc-2*CKSFrame.accelNormSq c := by
  dsimp only
  have hsc : actualFrameScalar G E x = CKSFrame.scalarCurvature (frameConnectionField G E x)
      (fun a => connectionFieldDerivative (frameConnectionField G E) (E a x) x) := by
    unfold actualFrameScalar CKSFrame.scalarCurvature
    simp_rw [physical_curvature_representation h]
  rw [hsc,CKSFrame.scalarCurvature_formula]

end
end CKSAngularGeometry

end

end OAI
