import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarOneAtom
import OAI.Probability.SKBarriers.Interpolation.FinitePressureAlgebra
import OAI.Probability.SKBarriers.Scalar.EmbeddedSites

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def pairSpinMap : (ℝ × ℝ) →L[ℝ] (Config 2 → ℝ) :=
  ContinuousLinearMap.pi (fun s => spin (s 0) • ContinuousLinearMap.fst ℝ ℝ ℝ+
    spin (s 1) • ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem pairSpinMap_apply (p : ℝ × ℝ) (s : Config 2) :
    pairSpinMap p s=spin (s 0)*p.1+spin (s 1)*p.2 := rfl

theorem pairSpin_terminal : siteValueTerminal (fun _ : Config 2 => 0) ∘ pairSpinMap=
    fun p => scalarSpinTerminal p.1+scalarSpinTerminal p.2 := by
  funext p
  have H := affineLogPartition_product 2 (fun (_ : Fin 2) (_ : Bool) => (0:ℝ))
    (fun i b => spin b • (if i=0 then ContinuousLinearMap.fst ℝ ℝ ℝ else ContinuousLinearMap.snd ℝ ℝ ℝ))
  have E := congrFun H p
  simp only [Fin.sum_univ_two,ite_true,show (1:Fin 2)≠0 by decide,ite_false,
    affineLogPartition_bool,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd'] at E
  simpa only [Function.comp_def,siteValueTerminal,affineLogPartition,zero_add,add_zero,
    pairSpinMap_apply,add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',scalarSpinTerminal] using E

def pairSpinObservable (s : Config 2) : ℝ := spin (s 0)*spin (s 1)

theorem pairSpinObservable_bound (s : Config 2) : |pairSpinObservable s|≤1 := by
  unfold pairSpinObservable spin
  split_ifs <;> norm_num

theorem pairSpin_thermal_observable :
    (affineMoment (fun _ : Config 2 => 0) (fun s => ContinuousLinearMap.proj s) pairSpinObservable) ∘ pairSpinMap=
      fun p => scalarMagnetization p.1*scalarMagnetization p.2 := by
  funext p
  unfold affineMoment affineGibbs
  simp only [Function.comp_def,ContinuousLinearMap.proj_apply,pairSpinMap_apply,zero_add]
  have HS (f : Config 2 → ℝ) : (∑ s, f s)=∑ a : Bool, ∑ b : Bool, f ![a,b] := by
    rw [← (finTwoArrowEquiv Bool).symm.sum_comp]
    simp only [Fintype.sum_prod_type,finTwoArrowEquiv_symm_apply]
  rw [HS]
  simp only [HS,Fintype.sum_bool,pairSpinObservable,Matrix.cons_val_zero,Matrix.cons_val_one,
    spin,Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul,mul_one,mul_neg_one,neg_neg]
  simp only [Real.exp_add,Real.exp_neg,scalarMagnetization,Real.sinh_eq,Real.cosh_eq]
  have ha := Real.exp_pos p.1
  have hb := Real.exp_pos p.2
  field_simp
  ring

end SK.Analytic

end
end

end OAI
