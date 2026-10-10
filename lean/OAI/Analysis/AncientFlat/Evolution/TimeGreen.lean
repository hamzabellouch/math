import OAI.Analysis.AncientFlat.Spectral.RecursionUnique

namespace OAI
noncomputable section
open Set
open scoped Topology BoundedContinuousFunction
namespace AncientMild
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def timeShift (a : ℝ) : C(ℝ,ℝ) := ⟨fun t => t-a,continuous_id.sub continuous_const⟩
def translate (a : ℝ) : (ℝ →ᵇ E) →L[ℂ] (ℝ →ᵇ E) :=
  BoundedContinuousFunction.compContinuousCLM E ℂ (timeShift (-a))
@[simp] lemma translate_apply (a : ℝ) (f : ℝ →ᵇ E) (t : ℝ) : translate a f t=f (t+a) := by
  change f (t-(-a))=f (t+a)
  rw [sub_neg_eq_add]
def trace (τ : ℝ) : (ℝ →ᵇ E) →L[ℂ] (ℤ →ᵇ E) :=
  BoundedContinuousFunction.compContinuousCLM E ℂ ⟨fun j => τ+(j:ℝ),continuous_of_discreteTopology⟩
@[simp] lemma trace_apply (τ : ℝ) (f : ℝ →ᵇ E) (j : ℤ) : trace τ f j=f (τ+(j:ℝ)) := rfl
def timeTerm (G : E →L[ℂ] E) (n : ℤ) : (ℝ →ᵇ E) →L[ℂ] (ℝ →ᵇ E) :=
  (G.compLeftContinuousBounded ℝ).comp (BoundedContinuousFunction.compContinuousCLM E ℂ (timeShift (n:ℝ)))
@[simp] lemma timeTerm_apply (G : E →L[ℂ] E) (n : ℤ) (f : ℝ →ᵇ E) (t : ℝ) :
    timeTerm G n f t=G (f (t-(n:ℝ))) := rfl
lemma timeTerm_norm (G : E →L[ℂ] E) (n : ℤ) : ‖timeTerm G n‖≤‖G‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G) (fun f => ?_)
  refine (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr ?_
  intro t
  exact G.le_opNorm_of_le (f.norm_coe_le_norm _)
variable [CompleteSpace E]
def timeGreen (G : ℤ → E →L[ℂ] E) : (ℝ →ᵇ E) →L[ℂ] (ℝ →ᵇ E) := ∑' n : ℤ, timeTerm (G n) n
lemma timeGreen_apply (G : ℤ → E →L[ℂ] E) (hG : Summable (fun n => ‖G n‖))
    (f : ℝ →ᵇ E) (t : ℝ) : timeGreen G f t=∑' n : ℤ, G n (f (t-(n:ℝ))) := by
  exact ((BoundedContinuousFunction.evalCLM ℂ t).comp
    (ContinuousLinearMap.apply ℂ (ℝ →ᵇ E) f)).map_tsum
      (Summable.of_norm_bounded hG (fun n => timeTerm_norm _ _))
lemma timeGreen_trace (G : ℤ → E →L[ℂ] E) (hG : Summable (fun n => ‖G n‖))
    (f : ℝ →ᵇ E) (τ : ℝ) : trace τ (timeGreen G f)=FlatRecursion.greenOperator G (trace τ f) := by
  ext j
  simp only [trace_apply,timeGreen_apply G hG,FlatRecursion.greenOperator_apply G hG]
  congr 1
  funext n
  simp only [Int.cast_sub,add_sub_assoc]
lemma timeGreen_solves (P : E →L[ℂ] E) (G : ℤ → E →L[ℂ] E)
    (hG : Summable (fun n => ‖G n‖))
    (hrec : ∀ n : ℤ, G (n+1)-P*G n=if n=0 then 1 else 0)
    (f : ℝ →ᵇ E) (τ : ℝ) : timeGreen G f (τ+1)=P (timeGreen G f τ)+f τ := by
  have he := FlatRecursion.greenOperator_solves P 1 G hG
    (by simpa only [one_smul] using hrec) (trace τ f) 0
  rw [← timeGreen_trace G hG f τ] at he
  simpa only [one_smul,trace_apply,zero_add,Int.cast_one,Int.cast_zero,add_zero] using he
lemma homogeneous_time_eq_zero (P : E →L[ℂ] E)
    (hc : ∀ z : ℂ, ‖z‖=1 → z ∈ resolventSet ℂ P)
    (f : ℝ →ᵇ E) (hf : ∀ τ : ℝ, f (τ+1)=P (f τ)) : f=0 := by
  ext τ
  have hz : trace τ f=0 := FlatRecursion.homogeneous_eq_zero P 1 zero_lt_one hc (trace τ f) (by
    intro j
    simpa only [Complex.ofReal_one,one_smul,trace_apply,Int.cast_add,Int.cast_one,←add_assoc] using hf (τ+(j:ℝ)))
  have hv := congrArg (fun g : ℤ →ᵇ E => g 0) hz
  simpa only [trace_apply,Int.cast_zero,add_zero,BoundedContinuousFunction.coe_zero,Pi.zero_apply] using hv
end AncientMild

end

end OAI
