import Mathlib
import OAI.Probability.Perceptron.Variational.LabelValue
import OAI.Probability.Perceptron.Control.StepControl

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma oneDim_inner (v : EuclideanSpace ℝ (Fin 1)) :
    inner ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1:ℝ))) v=v 0 := by
  simp [PiLp.inner_apply]

lemma oneDim_gaussian_average (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (a : ℝ) :
    (∫ v : EuclideanSpace ℝ (Fin 1), f (a+Real.sqrt s*v 0)
      ∂stdGaussian (EuclideanSpace ℝ (Fin 1)))=gaussianAverage s f a := by
  rw [gaussianAverage_scaling]
  have h : (∫ z, f (a+Real.sqrt s*z) ∂((stdGaussian (EuclideanSpace ℝ (Fin 1))).map
      (fun v => v 0)))=∫ v : EuclideanSpace ℝ (Fin 1), f (a+Real.sqrt s*v 0)
        ∂stdGaussian (EuclideanSpace ℝ (Fin 1)) :=
    integral_map (show Measurable (fun v : EuclideanSpace ℝ (Fin 1) => v 0) from by fun_prop).aemeasurable
      (show Measurable (fun z : ℝ => f (a+Real.sqrt s*z)) from by fun_prop).aestronglyMeasurable
  rw [stdGaussian_coordinate_law] at h
  exact h.symm

lemma oneDim_gaussian_entropic (s b : ℝ≥0) (f : ℝ →ᵇ ℝ) (x : EuclideanSpace ℝ (Fin 1)) :
    gaussianLinearEntropic (stdGaussian (EuclideanSpace ℝ (Fin 1))) b
      (diagonalMark (fun _ => Real.sqrt s)) (fun v => f (v 0)) x=heatLog s b f (x 0) := by
  have hX : ∀ a : ℝ, Integrable
      (fun v : EuclideanSpace ℝ (Fin 1) => Real.exp (a*f (x 0+Real.sqrt s*v 0)))
      (stdGaussian (EuclideanSpace ℝ (Fin 1))) := fun a =>
    boundedContinuousFunction_integrable_comp (expBCF a f) (by fun_prop)
  change entropicMean (stdGaussian (EuclideanSpace ℝ (Fin 1))) b
    (fun v => f (x 0+Real.sqrt s*v 0))=heatLog s b f (x 0)
  by_cases hb : b=0
  · subst b
    rw [NNReal.coe_zero,entropicMean_zero _ hX,heatLog,ite_eq_left rfl,oneDim_gaussian_average]
  · rw [entropicMean_eq_div _ hX (by exact_mod_cast hb),heatLog,ite_eq_right hb]
    unfold cgf mgf
    change Real.log (∫ v : EuclideanSpace ℝ (Fin 1), expBCF b f (x 0+Real.sqrt s*v 0)
      ∂stdGaussian (EuclideanSpace ℝ (Fin 1)))/(b:ℝ)=_
    rw [oneDim_gaussian_average]
    ring

lemma linearCascadeWord_congr {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : ℕ→E→L[ℝ] E) (k : ℕ) (z : Fin k→ℝ) (h : ∀ j<k,A j=B j) :
    linearCascadeWord A k z=linearCascadeWord B k z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [linearCascadeWord]
    rw [h k (Nat.lt_succ_self k),ih (fun i => z i.succ) (fun j hj => h j (Nat.lt_succ_of_lt hj))]

lemma profileGaussianStep_first {k : ℕ} (q : Fin (k+2)→Time) :
    profileGaussianStep (fun l (_ : Fin 1) => (q l:ℝ)) k=
      fun _ => Real.sqrt (timeSpan (q 0) (q 1)) := by
  funext i
  simp only [profileGaussianStep,dite_eq_left (Nat.lt_succ_self k)]
  have h0 : (⟨k+1-k-1,by omega⟩ : Fin (k+2))=0 := by ext; simp
  have h1 : (⟨k+1-k,by omega⟩ : Fin (k+2))=1 := by ext; simp
  rw [h0,h1]
  simp only [timeSpan,Real.coe_toNNReal']
  by_cases h : 0≤(q 1:ℝ)-q 0
  · rw [max_eq_left h]
  · have hn : (q 1:ℝ)-q 0≤0 := by linarith
    rw [max_eq_right hn,Real.sqrt_eq_zero_of_nonpos hn,Real.sqrt_zero]

lemma profileGaussianStep_tail {k : ℕ} (q : Fin (k+2)→Time) {j : ℕ} (hj : j<k) :
    profileGaussianStep (fun l (_ : Fin 1) => (q l:ℝ)) j=
      profileGaussianStep (fun l (_ : Fin 1) => (q l.succ:ℝ)) j := by
  funext i
  simp only [profileGaussianStep,dite_eq_left hj,dite_eq_left (Nat.lt_succ_of_lt hj)]
  have ha : (⟨k+1-j,by omega⟩ : Fin (k+2))=(⟨k-j,by omega⟩ : Fin (k+1)).succ := by
    ext; simp only [Fin.val_succ]; omega
  have hb : (⟨k+1-j-1,by omega⟩ : Fin (k+2))=(⟨k-j-1,by omega⟩ : Fin (k+1)).succ := by
    ext; simp only [Fin.val_succ]; omega
  rw [ha,hb]

lemma oneDim_profile_backward (g : Jet3) (k : ℕ) (q : Fin (k+1)→Time)
    (z : Fin k→ℝ≥0) (x : EuclideanSpace ℝ (Fin 1)) :
    gaussianLinearBackward (stdGaussian (EuclideanSpace ℝ (Fin 1)))
      (linearCascadeWord (fun j => diagonalMark (profileGaussianStep (fun l (_ : Fin 1) => (q l:ℝ)) j))
        k (fun i => z i)) (fun v => g.f (v 0)) x=(finiteStepControlJet g k q z).f (x 0) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [linearCascadeWord,gaussianLinearBackward,finiteStepControlJet]
    rw [profileGaussianStep_first]
    have hw := linearCascadeWord_congr
      (fun j => diagonalMark (profileGaussianStep (fun l (_ : Fin 1) => (q l:ℝ)) j))
      (fun j => diagonalMark (profileGaussianStep (fun l (_ : Fin 1) => (q l.succ:ℝ)) j))
      k (fun i => (z i.succ:ℝ)) (fun j hj => congrArg diagonalMark (profileGaussianStep_tail q hj))
    rw [hw]
    have hf := funext (ih (fun i => q i.succ) (fun i => z i.succ))
    rw [hf,oneDim_gaussian_entropic,Jet3.heatLog_f]
    change _=heatLog _ _ _ _
    rfl

lemma HeatChain.prepend {m : Trial} {g h j : Jet3} {a b c : Time}
    (H : HeatChain m g b c h) (J : HeatChain m h a b j) : HeatChain m g a c j := by
  induction J with
  | nil => exact H
  | cons d hat htb hm tail ih =>
    exact HeatChain.cons d hat (htb.trans H.left_le_right) hm (ih H)

lemma weightedStepTrial_controlValue_core (k : ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i,w i=1) (hq : Monotone q) (g : Jet3)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    controlValue P g.f (weightedStepTrial w q hw hw1)=
      ((finiteStepControlJet (g.heatLog (timeSpan (q (Fin.last k)) 1) 1) k q
        (weightedControlCoefficient k w hw)).heatLog (timeSpan 0 (q 0)) 0).f 0 := by
  let m := leftWeightedStepTrial w q hw hw1
  have ht : HeatChain m g (q (Fin.last k)) 1 (g.heatLog (timeSpan (q (Fin.last k)) 1) 1) := by
    rcases lt_or_eq_of_le (show q (Fin.last k)≤1 from le_top) with hl|he
    · apply HeatChain.cons 1 hl le_rfl _ (HeatChain.nil 1)
      intro r hr
      change (∑ i, if q i<r then w i else 0)=(1:ℝ)
      have hqr i : q i<r := (hq (Fin.le_last i)).trans_lt hr.1
      simp only [hqr,ite_true,hw1]
    · rw [he]
      simp only [timeSpan,sub_self,Real.toNNReal_zero,Jet3.heatLog_zero_time]
      exact HeatChain.nil 1
  have hm := finiteStepControlJet_chain (g.heatLog (timeSpan (q (Fin.last k)) 1) 1)
    m k q (weightedControlCoefficient k w hw) hq
    (fun i r hr => leftWeightedStepTrial_interval k w q hw hw1 hq i hr)
  have hm' := ht.prepend hm
  have H : HeatChain m g 0 1 ((finiteStepControlJet (g.heatLog (timeSpan (q (Fin.last k)) 1) 1)
      k q (weightedControlCoefficient k w hw)).heatLog (timeSpan 0 (q 0)) 0) := by
    rcases lt_or_eq_of_le (show (0:Time)≤q 0 from bot_le) with hl|he
    · apply HeatChain.cons 0 hl (show q 0≤1 from le_top) _ hm'
      intro r hr
      change (∑ i, if q i<r then w i else 0)=(0:ℝ)
      have hqr i : ¬ q i<r := not_lt_of_ge (hr.2.trans (hq (Fin.zero_le i)))
      simp only [hqr,ite_false,Finset.sum_const_zero]
    · rw [←he] at hm' ⊢
      simpa only [timeSpan,sub_self,Real.toNNReal_zero,Jet3.heatLog_zero_time] using hm'
  have he := leftWeightedStepTrial_ae w q hw hw1
  have hv := controlValue_trial_abs_sub_le P g.f (weightedStepTrial w q hw hw1) m ‖g.d1‖₊ g.lipschitz
  have hz : (∫ t, |weightedStepTrial w q hw hw1 t-m t| ∂timeLaw)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [he] with t ht
    simp only [m,ht,sub_self,abs_zero,Pi.zero_apply]
  rw [hz,mul_zero] at hv
  rw [sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hv (abs_nonneg _)))]
  exact H.controlValue_eq P hB

theorem labelProfileValue_control (k : ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0≤w i) (hw1 : ∑ i,w i=1) (hq : Monotone q) (g : Jet3)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    labelProfileValue k (stepCumulative w) (fun i => (q i:ℝ)) (q (Fin.last k)).prop.2 g=
      controlValue P g.f (weightedStepTrial w q hw hw1) := by
  rw [weightedStepTrial_controlValue_core k w q hw hw1 hq g P hB]
  have hend : (⟨1-(q (Fin.last k):ℝ),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0)=
      timeSpan (q (Fin.last k)) 1 := by
    apply Subtype.ext
    change 1-(q (Fin.last k):ℝ)=(timeSpan (q (Fin.last k)) 1:ℝ)
    exact (timeSpan_coe (show q (Fin.last k)≤1 from le_top)).symm
  have hstart : (timeSpan 0 (q 0):ℝ)=(q 0:ℝ) := by
    rw [timeSpan_coe (show (0:Time)≤q 0 from bot_le)]; simp
  have hterm : labelProfileTerminal g (timeSpan (q (Fin.last k)) 1)=
      fun v : EuclideanSpace ℝ (Fin 1) => (g.heatLog (timeSpan (q (Fin.last k)) 1) 1).f (v 0) := by
    funext v
    rw [labelProfileTerminal,oneDim_inner,Jet3.heatLog_f]
    rfl
  have hc : stepCumulative w=fun i => (weightedControlCoefficient k w hw i:ℝ) := rfl
  unfold labelProfileValue
  rw [hend,hterm,hc]
  simp_rw [oneDim_profile_backward]
  simp only [diagonalMark_apply,profileGaussianRoot]
  rw [Jet3.heatLog_f]
  change (∫ x : EuclideanSpace ℝ (Fin 1),
    (finiteStepControlJet (g.heatLog (timeSpan (q (Fin.last k)) 1) 1) k q
      (weightedControlCoefficient k w hw)).f (Real.sqrt (q 0:ℝ)*x 0)
      ∂stdGaussian (EuclideanSpace ℝ (Fin 1)))=heatLog (timeSpan 0 (q 0)) 0 _ 0
  rw [heatLog,ite_eq_left rfl]
  simpa only [hstart,zero_add] using oneDim_gaussian_average (timeSpan 0 (q 0))
    (finiteStepControlJet (g.heatLog (timeSpan (q (Fin.last k)) 1) 1) k q
      (weightedControlCoefficient k w hw)).f 0

end SphericalPerceptronFreeEnergy
end

end OAI
