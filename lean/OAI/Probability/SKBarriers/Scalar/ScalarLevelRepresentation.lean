import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarAverageCalculus

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def scalarLevelField : (n : ℕ) → (Fin n → ℝ) → Fin (n+1) → ParameterSpace n →L[ℝ] ℝ
  | 0,_,_ => ContinuousLinearMap.id ℝ ℝ
  | n+1,v,j => Fin.lastCases (scalarSpinField (n+1) v)
      (fun i => (scalarLevelField n (fun k => v k.castSucc) i).comp
        (ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ)) j

theorem scalarSpinField_succ (n : ℕ) (v : Fin (n+1) → ℝ) (z : ParameterSpace n) (y : ℝ) :
    scalarSpinField (n+1) v (z,y)=scalarSpinField n (fun i => v i.castSucc) z+v (Fin.last n)*y := by
  change parameter n z+coordinateLinear (n+1) v (z,y)=
    parameter n z+coordinateLinear n (fun i => v i.castSucc) z+v (Fin.last n)*y
  rw [coordinateLinear_apply (n+1),coordinateLinear_apply n,Fin.sum_univ_castSucc]
  simp only [coordinateProjection,Fin.lastCases_castSucc,Fin.lastCases_last,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
  ring

theorem gaussianStep_scalarSpinField (n : ℕ) (m : ℝ) (v : Fin (n+1) → ℝ) (f : ℝ → ℝ) :
    gaussianStep m (fun z => f (scalarSpinField (n+1) v z))=
      fun z => scalarStep m (v (Fin.last n)) f (scalarSpinField n (fun i => v i.castSucc) z) := by
  have he : (fun z : ParameterSpace (n+1) => f (scalarSpinField (n+1) v z)) =
      fun z : ParameterSpace n × ℝ => f (scalarSpinField n (fun i => v i.castSucc) z.1+v (Fin.last n)*z.2) := by
    funext z
    rw [scalarSpinField_succ n v z.1 z.2]
  rw [he]
  rfl

theorem hierarchyLevel_scalar_representation (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hspin : ScalarSpinConvex f) (j : Fin (n+1)) :
    ∃ F : ℝ → ℝ, BoundedDerivs F ∧ ScalarSpinConvex F ∧
      hierarchyLevel n m (fun z => f (scalarSpinField n v z)) j=
        fun z => F (scalarLevelField n v j z) := by
  induction n generalizing f with
  | zero => exact ⟨f,hf,hspin,by funext z; simp [hierarchyLevel,scalarLevelField,scalarSpinField,coordinateLinear,parameter]⟩
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact ⟨f,hf,hspin,by simp [hierarchyLevel,scalarLevelField]⟩
    · obtain ⟨F,hF,hS,hEq⟩ := ih (fun k => m k.castSucc) (fun k => v k.castSucc)
        (fun k => hm k.castSucc) (scalarStep_regular hf (m (Fin.last n)) (v (Fin.last n)))
        (hspin.scalarStep hf (hm (Fin.last n)) (v (Fin.last n))) i
      refine ⟨F,hF,hS,?_⟩
      simp only [hierarchyLevel,Fin.lastCases_castSucc,gaussianStep_scalarSpinField,hEq,
        scalarLevelField,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst']

theorem scalarLevelField_last (n : ℕ) (v : Fin n → ℝ) :
    scalarLevelField n v (Fin.last n)=scalarSpinField n v := by
  cases n with
  | zero => ext; simp [scalarLevelField,scalarSpinField,parameter,coordinateLinear]
  | succ n => simp [scalarLevelField]

theorem scalar_comp_directional {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (L : E →L[ℝ] ℝ) (z u : E) :
    fderiv ℝ (fun z => f (L z)) z u=rootGradient 0 f (L z)*L u ∧
      fderiv ℝ (fderiv ℝ (fun z => f (L z))) z u u=rootHessian 0 f (L z)*(L u)^2 := by
  have hd := hf.1.differentiable (by norm_num)
  have hF (z) : fderiv ℝ (fun z => f (L z)) z=(fderiv ℝ f (L z)).comp L :=
    ((hd _).hasFDerivAt.comp z L.hasFDerivAt).fderiv
  have he : fderiv ℝ (fun z => f (L z))=fun z => (fderiv ℝ f (L z)).comp L := funext hF
  constructor
  · rw [hF,ContinuousLinearMap.comp_apply]
    change fderiv ℝ f (L z) (L u)=fderiv ℝ f (L z) 1*L u
    rw [← smul_eq_mul,← map_smul]
    simp [smul_eq_mul,mul_comm]
  · rw [he]
    have hd' := (hf.1.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
    have H := ((hd' (L z)).hasFDerivAt.comp z L.hasFDerivAt).clm_comp (hasFDerivAt_const L z)
    change ((fderiv ℝ (fun y => (fderiv ℝ f ∘ ⇑L) y ∘L L) z) u) u = _
    rw [H.fderiv]
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_zero,zero_add]
    change fderiv ℝ (fderiv ℝ f) (L z) (L u) (L u)=
      fderiv ℝ (fderiv ℝ f) (L z) 1 1*(L u)^2
    have hd₁ : fderiv ℝ (fderiv ℝ f) (L z) (L u) = (L u) • fderiv ℝ (fderiv ℝ f) (L z) 1 := by
      simpa only [smul_eq_mul,mul_one] using (map_smul (fderiv ℝ (fderiv ℝ f) (L z)) (L u) (1:ℝ))
    have hd₂ : fderiv ℝ (fderiv ℝ f) (L z) 1 (L u) = (L u)*fderiv ℝ (fderiv ℝ f) (L z) 1 1 := by
      simpa only [smul_eq_mul,mul_one] using (map_smul (fderiv ℝ (fderiv ℝ f) (L z) 1) (L u) (1:ℝ))
    rw [hd₁,smul_apply,hd₂]
    simp only [smul_eq_mul]
    ring

theorem hierarchyLevel_scalar_direction_bounds (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hspin : ScalarSpinConvex f) (j : Fin (n+1)) (z u : ParameterSpace n) :
    |fderiv ℝ (hierarchyLevel n m (fun z => f (scalarSpinField n v z)) j) z u|≤
      |scalarLevelField n v j u| ∧
    |fderiv ℝ (fderiv ℝ (hierarchyLevel n m (fun z => f (scalarSpinField n v z)) j)) z u u|≤
      (scalarLevelField n v j u)^2 := by
  obtain ⟨F,hF,hS,he⟩ := hierarchyLevel_scalar_representation n m v hm hf hspin j
  rw [he]
  obtain ⟨h₁,h₂⟩ := scalar_comp_directional hF (scalarLevelField n v j) z u
  constructor
  · rw [h₁,abs_mul]
    exact (mul_le_mul_of_nonneg_right (hS.bounds _).1 (abs_nonneg _)).trans_eq (one_mul _)
  · rw [h₂,abs_mul,abs_of_nonneg (sq_nonneg (scalarLevelField n v j u))]
    exact (mul_le_mul_of_nonneg_right (hS.bounds _).2 (sq_nonneg _)).trans_eq (one_mul _)

end SK.Analytic

end
end

end OAI
