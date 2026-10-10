import OAI.Geometry.Relativity.CKS.NonroundFrame

namespace OAI

noncomputable section
namespace CKSFrame
noncomputable section
open scoped BigOperators Matrix

structure TensorData where
  L : ℝ
  eta : A → ℝ
  p : ℝ
  tau11 : ℝ
  tau12 : ℝ

def tensor (t : TensorData) : Matrix I I ℝ :=
  !![t.L,t.eta 0,t.eta 1;
    t.eta 0,t.p/2+t.tau11,t.tau12;
    t.eta 1,t.tau12,t.p/2-t.tau11]

def tangential (t : TensorData) : Matrix A A ℝ :=
  !![t.p/2+t.tau11,t.tau12;t.tau12,t.p/2-t.tau11]

def tau (t : TensorData) : Matrix A A ℝ :=
  !![t.tau11,t.tau12;t.tau12,-t.tau11]

def covariantTensor (c : ConnectionData) (t : TensorData) (dt : I → TensorData)
    (i j k : I) : ℝ := tensor (dt i) j k-
  ∑ a, (connection c i j a*tensor t a k+connection c i k a*tensor t j a)

def momentum (c : ConnectionData) (t : TensorData) (dt : I → TensorData) (j : I) : ℝ :=
  (∑ i, covariantTensor c t dt i i j)-∑ i, tensor (dt j) i i

def energy (c : ConnectionData) (dc : I → ConnectionData) (t : TensorData) : ℝ :=
  (scalarCurvature c dc+(∑ i, tensor t i i)^2-∑ i, ∑ j, (tensor t i j)^2)/2

def shearNormSq (c : ConnectionData) : ℝ :=
  (c.chi11-mean c/2)^2+2*c.chi12^2+(c.chi22-mean c/2)^2

def tauNormSq (t : TensorData) : ℝ := 2*t.tau11^2+2*t.tau12^2

def etaNormSq (t : TensorData) : ℝ := (t.eta 0)^2+(t.eta 1)^2

def shearTau (c : ConnectionData) (t : TensorData) : ℝ :=
  (c.chi11-c.chi22)*t.tau11+2*c.chi12*t.tau12

def etaAcceleration (c : ConnectionData) (t : TensorData) : ℝ :=
  ∑ a, t.eta a*c.B a

def etaDiv (c : ConnectionData) (t : TensorData) (dt : I → TensorData) : ℝ :=
  ∑ a, ((dt a.succ).eta a-∑ b, leafConnection c a a b*t.eta b)

def tauDiv (c : ConnectionData) (t : TensorData) (dt : I → TensorData) (a : A) : ℝ :=
  ∑ b, (tau (dt b.succ) b a-∑ e,
    (leafConnection c b b e*tau t e a+leafConnection c b a e*tau t b e))

def normalLieEta (c : ConnectionData) (t : TensorData) (dt : I → TensorData) (a : A) : ℝ :=
  (dt 0).eta a-∑ b, (connection c 0 a.succ b.succ-chi c a b)*t.eta b

def accelTensor (c : ConnectionData) (t : TensorData) (a : A) : ℝ :=
  t.L*c.B a-∑ b, tangential t b a*c.B b

lemma tensor_trace (t : TensorData) : (∑ i, tensor t i i) = t.L+t.p := by
  simp [tensor,Fin.sum_univ_succ]

lemma energy_decomposition (c : ConnectionData) (dc : I → ConnectionData) (t : TensorData) :
    energy c dc t = leafScalar c dc/2-normalMean dc+accelDiv c dc-accelNormSq c-
      3/4*(mean c)^2-shearNormSq c/2+t.L*t.p+t.p^2/4-tauNormSq t/2-etaNormSq t := by
  unfold energy
  rw [scalarCurvature_formula,tensor_trace]
  simp [tensor,Fin.sum_univ_succ,chiNormSq,shearNormSq,mean,tauNormSq,etaNormSq]
  ring

lemma normal_momentum_decomposition (c : ConnectionData) (t : TensorData) (dt : I → TensorData) :
    momentum c t dt 0 = mean c*(t.L-t.p/2)-shearTau c t-(dt 0).p+
      etaDiv c t dt-2*etaAcceleration c t := by
  simp [momentum,covariantTensor,tensor,connection,mean,shearTau,etaDiv,etaAcceleration,
    leafConnection,Fin.sum_univ_succ]
  ring

lemma tangential_momentum_decomposition (c : ConnectionData) (t : TensorData) (dt : I → TensorData)
    (a : A) : momentum c t dt a.succ = normalLieEta c t dt a+mean c*t.eta a+
      tauDiv c t dt a-((dt a.succ).L+(dt a.succ).p/2)+accelTensor c t a := by
  fin_cases a <;>
    simp [momentum,covariantTensor,tensor,connection,mean,normalLieEta,tauDiv,chi,tau,
      accelTensor,tangential,leafConnection,Fin.sum_univ_succ] <;> ring

theorem constraint_decomposition (c : ConnectionData) (dc : I → ConnectionData)
    (t : TensorData) (dt : I → TensorData) :
    energy c dc t = leafScalar c dc/2-normalMean dc+accelDiv c dc-accelNormSq c-
      3/4*(mean c)^2-shearNormSq c/2+t.L*t.p+t.p^2/4-tauNormSq t/2-etaNormSq t ∧
    momentum c t dt 0 = mean c*(t.L-t.p/2)-shearTau c t-(dt 0).p+
      etaDiv c t dt-2*etaAcceleration c t ∧
    ∀ a, momentum c t dt a.succ = normalLieEta c t dt a+mean c*t.eta a+
      tauDiv c t dt a-((dt a.succ).L+(dt a.succ).p/2)+accelTensor c t a :=
  ⟨energy_decomposition c dc t,normal_momentum_decomposition c t dt,
    tangential_momentum_decomposition c t dt⟩

end
end CKSFrame

end

end OAI
