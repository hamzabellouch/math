import OAI.Geometry.Relativity.CKS.NonroundConstraints
import OAI.Geometry.Relativity.CKS.PhysicalFrameCurvature

namespace OAI

noncomputable section
namespace CKSFrame
noncomputable section
open Matrix
open scoped BigOperators

def extractTensor (k : Matrix I I ℝ) : TensorData where
  L := k 0 0
  eta := ![k 0 1,k 0 2]
  p := k 1 1+k 2 2
  tau11 := (k 1 1-k 2 2)/2
  tau12 := k 1 2

lemma extractTensor_complete {k : Matrix I I ℝ} (hk : k.IsHermitian) :
    tensor (extractTensor k)=k := by
  have h10 := CKSAngularGeometry.hermitian_real_symmetry hk 0 1
  have h20 := CKSAngularGeometry.hermitian_real_symmetry hk 0 2
  have h21 := CKSAngularGeometry.hermitian_real_symmetry hk 1 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tensor,extractTensor] <;> linarith

end
end CKSFrame

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

def frameTensor (K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : AmbientMat := fun i j => metricPair (K x) (E i x) (E j x)

def frameTensorData (K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : CKSFrame.TensorData := CKSFrame.extractTensor (frameTensor K E x)

def frameTensorDerivativeData (K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (a : Fin 3) : CKSFrame.TensorData :=
  CKSFrame.extractTensor (fun i j => D (E a x) (fun y => frameTensor K E y i j) x)

lemma frameTensor_hermitian {K : PhysicalPoint → AmbientMat} (E : LocalFrame)
    {x : PhysicalPoint} (hk : (K x).IsHermitian) : (frameTensor K E x).IsHermitian := by
  ext i j
  change metricPair (K x) (E j x) (E i x)=metricPair (K x) (E i x) (E j x)
  exact metricPair_symm hk _ _

lemma frameTensorData_exact {K : PhysicalPoint → AmbientMat} (E : LocalFrame)
    {x : PhysicalPoint} (hk : (K x).IsHermitian) :
    CKSFrame.tensor (frameTensorData K E x)=frameTensor K E x :=
  CKSFrame.extractTensor_complete (frameTensor_hermitian E hk)

lemma frameTensorDerivativeData_exact {K : PhysicalPoint → AmbientMat} (E : LocalFrame)
    {x : PhysicalPoint} (hk : ∀ᶠ y in 𝓝 x, (K y).IsHermitian) (a : Fin 3) :
    CKSFrame.tensor (frameTensorDerivativeData K E x a)=
      (fun i j => D (E a x) (fun y => frameTensor K E y i j) x) := by
  apply CKSFrame.extractTensor_complete
  ext i j
  change D (E a x) (fun y => frameTensor K E y j i) x =
    D (E a x) (fun y => frameTensor K E y i j) x
  apply D_congr
  filter_upwards [hk] with y hy
  exact metricPair_symm hy _ _

def actualFrameTensorCovariant (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (i j k : Fin 3) : ℝ :=
  D (E i x) (fun y => frameTensor K E y j k) x -
    ∑ a, (frameCoefficient G E x i j a*frameTensor K E x a k+
      frameCoefficient G E x i k a*frameTensor K E x j a)

def actualFrameMomentum (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (j : Fin 3) : ℝ :=
  (∑ i, actualFrameTensorCovariant G K E x i i j)-
    ∑ i, D (E j x) (fun y => frameTensor K E y i i) x

def actualFrameEnergy (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : ℝ :=
  (actualFrameScalar G E x+(∑ i, frameTensor K E x i i)^2-
    ∑ i, ∑ j, (frameTensor K E x i j)^2)/2

lemma actualFrame_covariant_representation {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : ActualAdaptedAt G E x)
    (hk : ∀ᶠ y in 𝓝 x, (K y).IsHermitian) (i j k : Fin 3) :
    actualFrameTensorCovariant G K E x i j k = CKSFrame.covariantTensor
      (frameConnectionField G E x) (frameTensorData K E x)
      (frameTensorDerivativeData K E x) i j k := by
  unfold actualFrameTensorCovariant CKSFrame.covariantTensor
  rw [frame_connection_actual h, frameTensorData_exact E hk.self_of_nhds,
    frameTensorDerivativeData_exact E hk]

lemma actualFrame_momentum_representation {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : ActualAdaptedAt G E x)
    (hk : ∀ᶠ y in 𝓝 x, (K y).IsHermitian) (j : Fin 3) :
    actualFrameMomentum G K E x j = CKSFrame.momentum
      (frameConnectionField G E x) (frameTensorData K E x)
      (frameTensorDerivativeData K E x) j := by
  unfold actualFrameMomentum CKSFrame.momentum
  simp_rw [actualFrame_covariant_representation h hk,frameTensorDerivativeData_exact E hk]

lemma actualFrame_energy_representation {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : ∀ᶠ y in 𝓝 x, ActualAdaptedAt G E y)
    (hk : (K x).IsHermitian) :
    actualFrameEnergy G K E x = CKSFrame.energy
      (frameConnectionField G E x)
      (fun a => connectionFieldDerivative (frameConnectionField G E) (E a x) x)
      (frameTensorData K E x) := by
  unfold actualFrameEnergy CKSFrame.energy actualFrameScalar CKSFrame.scalarCurvature
  simp_rw [frameTensorData_exact E hk,physical_curvature_representation h]

end
end CKSAngularGeometry

end

end OAI
