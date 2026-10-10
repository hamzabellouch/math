import Mathlib
import OAI.Probability.SKBarriers.Scalar.TiltedTerminalLimit

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def scalarStepAverage (m v : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  gaussianAverage m (fun z : ℝ × ℝ => f (z.1+v*z.2))
    (fun z => g (z.1+v*z.2)) x

def scalarHierarchyAverage : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) →
    (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | 0,_,_,_,g => g
  | n+1,m,v,f,g => scalarHierarchyAverage n (fun i => m i.castSucc) (fun i => v i.castSucc)
      (scalarStep (m (Fin.last n)) (v (Fin.last n)) f)
      (scalarStepAverage (m (Fin.last n)) (v (Fin.last n)) f g)

theorem scalarParameterTerminal_succ (n : ℕ) (v : Fin (n+1) → ℝ)
    (F : ℝ → ℝ → ℝ) (x : ℝ) (z : ParameterSpace n) (y : ℝ) :
    scalarParameterTerminal (n+1) v F x (z,y) =
      F (parameter n z) ((x+coordinateLinear n (fun i => v i.castSucc) z)+v (Fin.last n)*y) := by
  unfold scalarParameterTerminal
  rw [coordinateLinear_apply (n+1),coordinateLinear_apply n,Fin.sum_univ_castSucc]
  simp only [coordinateProjection,Fin.lastCases_castSucc,Fin.lastCases_last,parameter,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',add_assoc]

theorem gaussianStep_scalarParameterTerminal (n : ℕ) (m : ℝ) (v : Fin (n+1) → ℝ)
    (F : ℝ → ℝ → ℝ) (x : ℝ) :
    gaussianStep m (scalarParameterTerminal (n+1) v F x) =
      scalarParameterTerminal n (fun i => v i.castSucc)
        (fun a => scalarStep m (v (Fin.last n)) (F a)) x := by
  funext z
  simp only [gaussianStep,positiveGaussianLogStep,scalarParameterTerminal_succ]
  rfl

theorem gaussianAverage_scalarParameterTerminal (n : ℕ) (m : ℝ) (v : Fin (n+1) → ℝ)
    (F H : ℝ → ℝ → ℝ) (x : ℝ) :
    gaussianAverage m (scalarParameterTerminal (n+1) v F x)
      (scalarParameterTerminal (n+1) v H x) =
      scalarParameterTerminal n (fun i => v i.castSucc)
        (fun a => scalarStepAverage m (v (Fin.last n)) (F a) (H a)) x := by
  funext z
  simp only [gaussianAverage,gaussianStepLaw,scalarParameterTerminal_succ]
  rfl

theorem hierarchyAverage_scalarParameterTerminal (n : ℕ) (m v : Fin n → ℝ)
    (F H : ℝ → ℝ → ℝ) (x a : ℝ) :
    hierarchyAverage n m (scalarParameterTerminal n v F x) (scalarParameterTerminal n v H x) a =
      scalarHierarchyAverage n m v (F a) (H a) x := by
  induction n generalizing F H with
  | zero => simp [hierarchyAverage,scalarHierarchyAverage,scalarParameterTerminal,parameter,coordinateLinear]
  | succ n ih =>
    simp only [hierarchyAverage,gaussianStep_scalarParameterTerminal,
      gaussianAverage_scalarParameterTerminal,scalarHierarchyAverage,ih]

theorem scalarHierarchyAverage_eq_integral (n : ℕ) (m v : Fin n → ℝ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : Continuous g) {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ y, |g y| ≤ B) (x : ℝ) :
    scalarHierarchyAverage n m v f g x =
      ∫ z, g (x+coordinateLinear n v z) ∂hierarchyPathLaw n m
        (fun z => f (x+coordinateLinear n v z)) 0 := by
  rw [← hierarchyAverage_scalarParameterTerminal n m v (fun _ => f) (fun _ => g) x 0]
  exact hierarchyAverage_eq_integral n m _ ((hf.translate x).compCLM (coordinateLinear n v)) _
    (hg.comp (continuous_const.add (coordinateLinear n v).continuous)) hB
    (fun z => by simpa only [Real.norm_eq_abs,scalarParameterTerminal,Function.comp_apply,Pi.add_apply] using hb (x+coordinateLinear n v z)) 0

theorem scalarHierarchy_primitive_derivative (n : ℕ) (m v : Fin n → ℝ)
    {f G g : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (x a : ℝ) :
    deriv (fun b => scalarHierarchy n m v (primitivePerturbation f G b) x) a =
      scalarHierarchyAverage n m v (primitivePerturbation f G a) (fun y => g (y+a)) x := by
  rw [← funext (hierarchyPressure_scalarParameterTerminal n m v (primitivePerturbation f G) x)]
  change rootGradient 0 _ a = _
  rw [hierarchyPressure_rootGradient n m (primitiveParameterTerminal_regular n v hf hG x)]
  have he : rootGradient n (scalarParameterTerminal n v (primitivePerturbation f G) x) =
      scalarParameterTerminal n v (fun a y => g (y+a)) x :=
    funext (primitiveParameterTerminal_rootGradient n v hf hG hg x)
  rw [he,hierarchyAverage_scalarParameterTerminal]

@[simp] theorem primitivePerturbation_zero (f G : ℝ → ℝ) : primitivePerturbation f G 0=f := by
  funext y
  simp only [primitivePerturbation,add_zero,add_sub_cancel_right]

def dyadicScalarAverage (β : ℝ) (α : ℝ → ℝ) (n : ℕ) (s : ℝ) (t : ℝ≥0)
    (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  let l := dyadicIntervals α n s t
  scalarHierarchyAverage l.length (fun i => (l.get i).1)
    (fun i => β*Real.sqrt ((l.get i).2:ℝ)) f g x

theorem dyadicScalar_primitive_derivative_zero (β : ℝ) (α : ℝ → ℝ) (n : ℕ) (s : ℝ) (t : ℝ≥0)
    {f G g : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (x : ℝ) :
    deriv (fun b => dyadicScalar β α n s t (primitivePerturbation f G b) x) 0 =
      dyadicScalarAverage β α n s t f g x := by
  simp only [dyadicScalar,scalarTimeChain_eq_hierarchy]
  rw [scalarHierarchy_primitive_derivative _ _ _ hf hG hg,primitivePerturbation_zero]
  simp only [add_zero,dyadicScalarAverage]

def scalarCDFAverage (β : ℝ) (α : ℝ → ℝ) (s : ℝ) (t : ℝ≥0) (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  limUnder atTop (fun n => dyadicScalarAverage β α n s t f g x)

theorem scalarCDFAverage_eq_terminalDerivative (β : ℝ) (α : ℝ → ℝ) (s : ℝ) (t : ℝ≥0)
    {f G g : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (x : ℝ) :
    scalarCDFAverage β α s t f g x=scalarCDFTerminalDerivative β α s t f G x 0 := by
  simp only [scalarCDFAverage,scalarCDFTerminalDerivative,
    dyadicScalar_primitive_derivative_zero β α _ s t hf hG hg x]

theorem dyadicScalarAverage_tendsto (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f G g dg : ℝ → ℝ} (hf : BoundedDerivs f) (hG : BoundedDerivs G)
    (hg : ∀ y, HasDerivAt G (g y) y) (hdg : ∀ y, HasDerivAt g (dg y) y)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f) (hGB : LipschitzWith B G)
    (hB : ∀ y, |g y| ≤ B) (hC : ∀ y, |dg y| ≤ C)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    Tendsto (fun n => dyadicScalarAverage β α n s t f g x) atTop
      (𝓝 (scalarCDFAverage β α s t f g x)) := by
  have H := (dyadicScalar_terminal_derivative_uniform β hα hmono hf hG hg hdg hfK hGB hB hC s t ht x).tendsto_at 0
  simpa only [dyadicScalar_primitive_derivative_zero β α _ s t hf hG hg x,
    ← scalarCDFAverage_eq_terminalDerivative β α s t hf hG hg x] using H

end SK.Analytic

end
end

end OAI
