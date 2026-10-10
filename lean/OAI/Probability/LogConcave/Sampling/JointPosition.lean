import Mathlib
import OAI.Probability.LogConcave.JetEstimates.NormalizedLaplace
import OAI.Probability.LogConcave.Sampling.PrimitiveField

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

def jointPosition (d : ℕ) : Point d →L[ℝ] JointPoint d :=
  EuclideanSpace.sumEquivProd.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ _)

def jointField (d : ℕ) : Point d →L[ℝ] JointPoint d :=
  EuclideanSpace.sumEquivProd.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ _ _)

lemma jointPair_inner {d : ℕ} (u v w z : Point d) :
    inner ℝ (EuclideanSpace.sumEquivProd.symm (u,v) : JointPoint d)
      (EuclideanSpace.sumEquivProd.symm (w,z)) = inner ℝ u w+inner ℝ v z := by
  have he := jointImage_norm_sq (u+w) (v+z)
  rw [show (u+w,v+z)=(u,v)+(w,z) from rfl,map_add,norm_add_sq_real] at he
  rw [jointImage_norm_sq,jointImage_norm_sq,norm_add_sq_real,norm_add_sq_real] at he
  linarith

lemma jointPosition_inner {d : ℕ} (u : Point d) (f : Point d → Point d) (L : ℝ) (z : Point d) :
    inner ℝ (jointPosition d u) (jointImage f L z)=inner ℝ u z := by
  change inner ℝ (EuclideanSpace.sumEquivProd.symm (u,0) : JointPoint d)
      (EuclideanSpace.sumEquivProd.symm (z,L⁻¹ • f z))=_
  rw [jointPair_inner,inner_zero_left,add_zero]

lemma jointField_inner {d : ℕ} (u : Point d) (f : Point d → Point d) (L : ℝ) (z : Point d) :
    inner ℝ (jointField d u) (jointImage f L z)=L⁻¹*inner ℝ u (f z) := by
  change inner ℝ (EuclideanSpace.sumEquivProd.symm (0,u) : JointPoint d)
      (EuclideanSpace.sumEquivProd.symm (z,L⁻¹ • f z))=_
  rw [jointPair_inner,inner_zero_left,zero_add,inner_smul_right]

lemma jointPosition_basis {d : ℕ} (i : Fin d) :
    jointPosition d ((EuclideanSpace.basisFun (Fin d) ℝ) i)=
      (EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ) (Sum.inl i) := by
  simp only [EuclideanSpace.basisFun_apply]
  ext j
  cases j with
  | inl j =>
    change (EuclideanSpace.single i (1:ℝ)) j=(EuclideanSpace.single (Sum.inl i : Fin d ⊕ Fin d) (1:ℝ)) (Sum.inl j)
    simp [PiLp.single_apply]
  | inr j =>
    change (0:ℝ)=(EuclideanSpace.single (Sum.inl i : Fin d ⊕ Fin d) (1:ℝ)) (Sum.inr j)
    simp

lemma jointField_basis {d : ℕ} (i : Fin d) :
    jointField d ((EuclideanSpace.basisFun (Fin d) ℝ) i)=
      (EuclideanSpace.basisFun (Fin d ⊕ Fin d) ℝ) (Sum.inr i) := by
  simp only [EuclideanSpace.basisFun_apply]
  ext j
  cases j with
  | inl j =>
    change (0:ℝ)=(EuclideanSpace.single (Sum.inr i : Fin d ⊕ Fin d) (1:ℝ)) (Sum.inl j)
    simp
  | inr j =>
    change (EuclideanSpace.single i (1:ℝ)) j=(EuclideanSpace.single (Sum.inr i : Fin d ⊕ Fin d) (1:ℝ)) (Sum.inr j)
    simp [PiLp.single_apply]

lemma joint_laplace_one {d : ℕ} {μ : Measure (Point d)} {f : Point d → Point d}
    (hf : Continuous f) (L : ℝ) (θ : Point d) :
    Appell.laplace (μ.map (jointImage f L)) (fun _ => (1:ℝ)) (jointPosition d θ)=
      Appell.laplace μ (fun _ => (1:ℝ)) θ := by
  have hS : Continuous (jointImage f L) := by
    unfold jointImage
    fun_prop
  rw [Appell.laplace,integral_map hS.aemeasurable (by fun_prop)]
  simp only [jointPosition_inner,Appell.laplace]

lemma joint_normalizedLaplace {d : ℕ} {μ : Measure (Point d)} {f : Point d → Point d}
    (hf : Continuous f) (L : ℝ) (u θ : Point d) :
    Appell.normalizedLaplace (μ.map (jointImage f L))
      (fun z => inner ℝ (jointField d u) z) (jointPosition d θ)=
      L⁻¹*Appell.normalizedLaplace μ (fun z => inner ℝ u (f z)) θ := by
  have hS : Continuous (jointImage f L) := by
    unfold jointImage
    fun_prop
  have hn : Appell.laplace (μ.map (jointImage f L))
      (fun z => inner ℝ (jointField d u) z) (jointPosition d θ)=
      L⁻¹*Appell.laplace μ (fun z => inner ℝ u (f z)) θ := by
    rw [Appell.laplace,integral_map hS.aemeasurable (by fun_prop)]
    simp only [jointPosition_inner,jointField_inner,smul_eq_mul]
    rw [show (fun z : Point d => Real.exp (inner ℝ θ z)*(L⁻¹*inner ℝ u (f z)))=
      fun z => L⁻¹*(Real.exp (inner ℝ θ z)*inner ℝ u (f z)) by funext z; ring,
      integral_const_mul,Appell.laplace]
    rfl
  unfold Appell.normalizedLaplace
  rw [joint_laplace_one hf,hn]
  ring

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
