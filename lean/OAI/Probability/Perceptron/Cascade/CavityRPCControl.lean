import Mathlib
import OAI.Probability.Perceptron.Control.LabelProfileControl
import OAI.Probability.Perceptron.Cascade.CavityFiniteRPC

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma cavity_scalar_vector_recursion (τ : ℕ→ℝ) (F : ℝ→ᵇℝ)
    (k : ℕ) (z : Fin k→ℝ) (x : ℕ→Spin 1) :
    finiteCascadeLogRecursion (gaussianMarkLaw : ProbabilityMeasure (Spin 1))
      (gaussianLinearMarkStep (fun j=>diagonalMark (fun _ : Fin 1=>τ j))) k z
      (fun x=>F (x 0 0)) x=
    finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep τ) k z
      (fun x=>F (x 0)) (fun j=>x j 0) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [finiteCascadeLogRecursion,fractionalLogMoment,ih]
    congr 2
    let G := fun b : ℝ=>Real.exp (z 0*finiteCascadeLogRecursion standardGaussianMark
      (gaussianShiftStep τ) k (fun i=>z i.succ) (fun x=>F (x 0))
        (gaussianShiftStep τ ((fun j=>x j 0),b)))
    have hm := finiteCascadeLogRecursion_measurable standardGaussianMark (gaussianShiftStep τ)
      (gaussianShiftStep_measurable τ) k (fun i=>z i.succ)
      (F.measurable.comp (measurable_pi_apply 0))
    have hG : Measurable G := Real.measurable_exp.comp (measurable_const.mul
      (hm.comp ((gaussianShiftStep_measurable τ).comp (measurable_const.prodMk measurable_id))))
    have he := integral_map (μ:=stdGaussian (Spin 1)) (show Measurable (fun v : Spin 1=>v 0) from by fun_prop).aemeasurable
      hG.aestronglyMeasurable
    rw [stdGaussian_coordinate_law] at he
    exact he.symm

lemma cavityScalarRootValue_eq_label (k : ℕ) (z : Fin k→ℝ) (hz0 : ∀ i,0<z i)
    (q : Fin (k+1)→ℝ) (hq1 : q (Fin.last k)≤1) (g : Jet3) :
    cavityScalarRootValue k (fun j=>profileGaussianStep (fun l (_ : Fin 1)=>q l) j 0)
      z (Real.sqrt (q 0)) (g.heatLog ⟨1-q (Fin.last k),sub_nonneg.mpr hq1⟩ 1).f=
      labelProfileValue k z q hq1 g := by
  let s : ℝ≥0 := ⟨1-q (Fin.last k),sub_nonneg.mpr hq1⟩
  let τ := fun j=>profileGaussianStep (fun l (_ : Fin 1)=>q l) j 0
  let A := fun j=>diagonalMark (profileGaussianStep (fun l (_ : Fin 1)=>q l) j)
  have hA : (fun j=>diagonalMark (fun _ : Fin 1=>τ j))=A := by
    rfl
  have hF : (fun v : Spin 1=>(g.heatLog s 1).f (v 0))=labelProfileTerminal g s := by
    funext v
    rw [labelProfileTerminal,oneDim_inner,Jet3.heatLog_f]
    rfl
  let : IsGaussian (gaussianMarkLaw (E:=Spin 1) : Measure (Spin 1)) :=
    (inferInstance : IsGaussian (stdGaussian (Spin 1)))
  have hr := (gaussianLinearRecursion_realization (gaussianMarkLaw (E:=Spin 1)) A
    (labelProfileTerminal_lipschitz g s) k z hz0).1
  have hs (v : Spin 1) :
      finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep τ) k z
        (fun x=>(g.heatLog s 1).f (x 0)) (fun _=>Real.sqrt (q 0)*v 0)=
      gaussianLinearBackward (stdGaussian (Spin 1)) (linearCascadeWord A k z)
        (labelProfileTerminal g s) (diagonalMark (profileGaussianRoot (fun l (_ : Fin 1)=>q l)) v) := by
    have H := cavity_scalar_vector_recursion τ (g.heatLog s 1).f k z
      (fun _=>diagonalMark (profileGaussianRoot (fun l (_ : Fin 1)=>q l)) v)
    rw [hA] at H
    have ht : (fun x : ℕ→Spin 1=>(g.heatLog s 1).f (x 0 0))=
        fun x=>labelProfileTerminal g s (x 0) := funext (fun x=>congrFun hF (x 0))
    rw [ht,hr] at H
    exact H.symm
  unfold cavityScalarRootValue labelProfileValue
  change (∫ b,finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep τ) k z
    (fun x=>(g.heatLog s 1).f (x 0)) (fun _=>Real.sqrt (q 0)*b)
      ∂(standardGaussianMark : Measure ℝ))=_
  have hm := finiteCascadeLogRecursion_measurable standardGaussianMark (gaussianShiftStep τ)
    (gaussianShiftStep_measurable τ) k z ((g.heatLog s 1).f.measurable.comp (measurable_pi_apply 0))
  have hroot : Measurable (fun b : ℝ=>finiteCascadeLogRecursion standardGaussianMark
      (gaussianShiftStep τ) k z (fun x=>(g.heatLog s 1).f (x 0))
        (fun _=>Real.sqrt (q 0)*b)) :=
    hm.comp (Measurable.of_eval (fun _=>measurable_const.mul measurable_id))
  have he := integral_map (μ:=stdGaussian (Spin 1)) (show Measurable (fun v : Spin 1=>v 0) from by fun_prop).aemeasurable
    hroot.aestronglyMeasurable
  rw [stdGaussian_coordinate_law] at he
  exact he.trans (integral_congr_ae (ae_of_all _ hs))

theorem cavityScalarRootValue_control (k : ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i,0≤w i) (hw1 : ∑ i,w i=1) (hq : Monotone q)
    (hz0 : ∀ i,0<stepCumulative w i) (g : Jet3)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    cavityScalarRootValue k (fun j=>profileGaussianStep (fun l (_ : Fin 1)=>(q l:ℝ)) j 0)
      (stepCumulative w) (Real.sqrt (q 0 : ℝ))
      (g.heatLog ⟨1-(q (Fin.last k):ℝ),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ 1).f=
      controlValue P g.f (weightedStepTrial w q hw hw1) := by
  rw [cavityScalarRootValue_eq_label k (stepCumulative w) hz0]
  exact labelProfileValue_control k w q hw hw1 hq g P hB

end SphericalPerceptronFreeEnergy
end

end OAI
