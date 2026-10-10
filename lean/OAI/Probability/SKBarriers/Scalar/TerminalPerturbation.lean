import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarHierarchy
import OAI.Probability.SKBarriers.Hierarchy.RootCalculus

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def primitivePerturbation (f G : ℝ → ℝ) (a y : ℝ) : ℝ :=
  f y+G (y+a)-G y

def scalarParameterTerminal (n : ℕ) (v : Fin n → ℝ) (F : ℝ → ℝ → ℝ)
    (x : ℝ) (z : ParameterSpace n) : ℝ := F (parameter n z) (x+coordinateLinear n v z)

theorem hierarchyPressure_scalarParameterTerminal (n : ℕ) (m v : Fin n → ℝ)
    (F : ℝ → ℝ → ℝ) (x a : ℝ) :
    hierarchyPressure n m (scalarParameterTerminal n v F x) a =
      scalarHierarchy n m v (F a) x := by
  induction n generalizing F with
  | zero => simp [hierarchyPressure,scalarParameterTerminal,scalarHierarchy,parameter,coordinateLinear]
  | succ n ih =>
    have he : gaussianStep (m (Fin.last n)) (scalarParameterTerminal (n+1) v F x) =
        scalarParameterTerminal n (fun i => v i.castSucc)
          (fun a => scalarStep (m (Fin.last n)) (v (Fin.last n)) (F a)) x := by
      funext z
      have harg (y : ℝ) : scalarParameterTerminal (n+1) v F x (z,y) =
          F (parameter n z) ((x+coordinateLinear n (fun i => v i.castSucc) z)+v (Fin.last n)*y) := by
        unfold scalarParameterTerminal
        rw [coordinateLinear_apply (n+1),coordinateLinear_apply n,Fin.sum_univ_castSucc]
        simp only [coordinateProjection,Fin.lastCases_castSucc,Fin.lastCases_last,parameter,
          ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',add_assoc]
      simp only [gaussianStep,positiveGaussianLogStep,scalarParameterTerminal,scalarStep]
      simp only [scalarParameterTerminal] at harg
      simp_rw [harg]
    change hierarchyPressure n (fun i => m i.castSucc) _ a = _
    rw [he,ih]
    rfl

theorem primitivePerturbation_regular {f G : ℝ → ℝ} (hf : BoundedDerivs f)
    (hG : BoundedDerivs G) (a : ℝ) : BoundedDerivs (primitivePerturbation f G a) := by
  change BoundedDerivs (fun y => f y+G (y+a)-G y)
  simpa only [neg_one_mul,sub_eq_add_neg,add_comm a] using
    (hf.add (hG.translate a)).add (hG.const_mul (-1))

theorem primitivePerturbation_lipschitz {f G : ℝ → ℝ} {K B : ℝ≥0}
    (hf : LipschitzWith K f) (hG : LipschitzWith B G) (a : ℝ) :
    LipschitzWith (K+B+B) (primitivePerturbation f G a) := by
  have ht : LipschitzWith B (fun y => G (y+a)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [Real.dist_eq,add_sub_add_right_eq_sub] using hG.dist_le_mul (y+a) (z+a)
  exact (hf.add ht).sub hG

theorem primitiveParameterTerminal_regular (n : ℕ) (v : Fin n → ℝ)
    {f G : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G) (x : ℝ) :
    BoundedDerivs (scalarParameterTerminal n v (primitivePerturbation f G) x) := by
  have H := (((hf.translate x).compCLM (coordinateLinear n v)).add
    ((hG.translate x).compCLM (coordinateLinear n v+parameter n))).add
    (((hG.translate x).compCLM (coordinateLinear n v)).const_mul (-1))
  convert H using 1
  funext z
  simp only [scalarParameterTerminal,primitivePerturbation,add_apply,neg_one_mul,add_assoc]
  ring

theorem primitiveParameterTerminal_rootGradient (n : ℕ) (v : Fin n → ℝ)
    {f G g : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (x : ℝ) (z : ParameterSpace n) :
    rootGradient n (scalarParameterTerminal n v (primitivePerturbation f G) x) z =
      g (x+coordinateLinear n v z+parameter n z) := by
  have hd := rootLine_hasDerivAt n (primitiveParameterTerminal_regular n v hf hG x) z 0
  have he : (fun a : ℝ => scalarParameterTerminal n v (primitivePerturbation f G) x
      (z+a • parameterAxis n)) = fun a =>
      f (x+coordinateLinear n v z)+G (x+coordinateLinear n v z+parameter n z+a)-
        G (x+coordinateLinear n v z) := by
    funext a
    simp only [scalarParameterTerminal,primitivePerturbation,map_add,map_smul,
      coordinateLinear_axis,parameter_axis,smul_eq_mul,mul_zero,add_zero,mul_one,add_assoc]
  rw [he,zero_smul,add_zero] at hd
  have hd' := (hg (x+coordinateLinear n v z+parameter n z+0)).comp 0
    ((hasDerivAt_id 0).const_add (x+coordinateLinear n v z+parameter n z))
  simp only [add_zero,mul_one] at hd'
  exact hd.unique ((hd'.const_add _).sub_const _)

theorem primitiveParameterTerminal_rootHessian (n : ℕ) (v : Fin n → ℝ)
    {f G g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (hdg : ∀ y, HasDerivAt g (dg y) y)
    (x : ℝ) (z : ParameterSpace n) :
    rootHessian n (scalarParameterTerminal n v (primitivePerturbation f G) x) z =
      dg (x+coordinateLinear n v z+parameter n z) := by
  have hd := rootGradientLine_hasDerivAt n (primitiveParameterTerminal_regular n v hf hG x) z 0
  have he : (fun a : ℝ => rootGradient n (scalarParameterTerminal n v
      (primitivePerturbation f G) x) (z+a • parameterAxis n)) = fun a =>
      g (x+coordinateLinear n v z+parameter n z+a) := by
    funext a
    rw [primitiveParameterTerminal_rootGradient n v hf hG hg]
    simp only [map_add,map_smul,coordinateLinear_axis,parameter_axis,
      smul_eq_mul,mul_zero,add_zero,mul_one,add_assoc]
  rw [he,zero_smul,add_zero] at hd
  have hd' := (hdg (x+coordinateLinear n v z+parameter n z+0)).comp 0
    ((hasDerivAt_id 0).const_add (x+coordinateLinear n v z+parameter n z))
  simp only [add_zero,mul_one] at hd'
  exact hd.unique hd'

end SK.Analytic

end
end

end OAI
