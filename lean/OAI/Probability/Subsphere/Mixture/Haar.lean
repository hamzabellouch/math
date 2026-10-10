import Mathlib
import OAI.Probability.Subsphere.Regression.Spheres

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

instance orthogonal_probability : IsProbabilityMeasure (orthogonalLaw (E := E)) :=
  ⟨Measure.haarMeasure_self⟩

instance orthogonal_haar : (orthogonalLaw (E := E)).IsHaarMeasure := by
  unfold orthogonalLaw
  infer_instance

instance orthogonal_right : (orthogonalLaw (E := E)).IsMulRightInvariant := by
  constructor
  intro u
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

def act (u : Orthogonal E) (x : E) : E := (u.val : E →L[ℝ] E) x

lemma continuous_act : Continuous (fun z : Orthogonal E × E => act z.1 z.2) := by
  unfold act
  fun_prop

lemma act_mul (u v : Orthogonal E) (x : E) : act (u*v) x = act u (act v x) := rfl

lemma act_one (x : E) : act (1 : Orthogonal E) x = x := rfl

lemma act_norm (u : Orthogonal E) (x : E) : ‖act u x‖ = ‖x‖ := Unitary.norm_map u x

lemma exists_act {x y : E} (h : ‖x‖ = ‖y‖) : ∃ u : Orthogonal E, act u x = y := by
  let e := (ℝ ∙ (x-y))ᗮ.reflection
  refine ⟨Unitary.linearIsometryEquiv.symm e,?_⟩
  change Unitary.linearIsometryEquiv (Unitary.linearIsometryEquiv.symm e) x = y
  rw [MulEquiv.apply_symm_apply]
  exact Submodule.reflection_sub h

variable [MeasurableSpace E] [BorelSpace E]

lemma haar_integral_independent {x y : E} (h : ‖x‖ = ‖y‖)
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ u, f (act u x) ∂orthogonalLaw) = ∫⁻ u, f (act u y) ∂orthogonalLaw := by
  obtain ⟨v,hv⟩ := exists_act h
  have hr := measurePreserving_mul_right (orthogonalLaw (E := E)) v
  have hf' : Measurable (fun u : Orthogonal E => f (act u x)) :=
    hf.comp (continuous_act.comp (continuous_id.prodMk continuous_const)).measurable
  simpa only [Function.comp_def,act_mul,hv] using (hr.lintegral_comp hf').symm

lemma haar_eval_integral [Nontrivial E] {x : E} (hx : ‖x‖ = 1)
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ u, f (act u x) ∂orthogonalLaw) = ∫⁻ y, f y ∂SubsphereRegression.ambientSphereLaw := by
  have hm : Measurable (fun z : E × Orthogonal E => f (act z.2 z.1)) :=
    hf.comp (continuous_act.comp continuous_swap).measurable
  have he : (∫⁻ y, ∫⁻ u, f (act u y) ∂orthogonalLaw ∂SubsphereRegression.ambientSphereLaw) =
      ∫⁻ _ : E, (∫⁻ u, f (act u x) ∂orthogonalLaw) ∂SubsphereRegression.ambientSphereLaw := by
    apply lintegral_congr_ae
    filter_upwards [SubsphereRegression.ambientSphereLaw_ae_norm] with y hy
    exact haar_integral_independent (hy.trans hx.symm) hf
  have hrot (u : Orthogonal E) :
      (∫⁻ y, f (act u y) ∂SubsphereRegression.ambientSphereLaw) =
      ∫⁻ y, f y ∂SubsphereRegression.ambientSphereLaw :=
    (SubsphereRegression.ambientSphereLaw_isometry (Unitary.linearIsometryEquiv u)).lintegral_comp hf
  rw [lintegral_lintegral_swap hm.aemeasurable] at he
  simp_rw [hrot] at he
  simpa using he.symm

lemma haar_eval_preserving [Nontrivial E] {x : E} (hx : ‖x‖ = 1) :
    MeasurePreserving (fun u : Orthogonal E => act u x) orthogonalLaw
      SubsphereRegression.ambientSphereLaw := by
  refine ⟨(continuous_act.comp (continuous_id.prodMk continuous_const)).measurable,?_⟩
  apply Measure.ext
  intro s hs
  have hm : Measurable (fun u : Orthogonal E => act u x) :=
    (continuous_act.comp (continuous_id.prodMk continuous_const)).measurable
  rw [Measure.map_apply hm hs]
  have hi := haar_eval_integral hx ((measurable_const : Measurable (fun _ : E => (1 : ℝ≥0∞))).indicator hs)
  have he : (fun u : Orthogonal E => s.indicator (fun _ => (1 : ℝ≥0∞)) (act u x)) =
      ((fun u : Orthogonal E => act u x) ⁻¹' s).indicator (fun _ => 1) := by
    funext u
    by_cases h : act u x ∈ s <;> simp [Set.indicator,h]
  rw [he,lintegral_indicator_const (hs.preimage hm),lintegral_indicator_const hs] at hi
  simpa using hi

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma blockIso_apply (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) (x : E) :
    blockIso V u w x = (act (E := V) u (V.orthogonalProjectionOnto x) : E) +
      (act (E := Vᗮ) w (Vᗮ.orthogonalProjectionOnto x) : E) := by
  simp only [blockIso,LinearIsometryEquiv.trans_apply,Submodule.orthogonalDecomposition_symm_apply,
    Submodule.orthogonalDecomposition_apply,LinearIsometryEquiv.withLpProdCongr_apply]
  rfl

lemma continuous_blockIso (V : Submodule ℝ E) :
    Continuous (fun z : (Orthogonal V × Orthogonal Vᗮ) × E => blockIso V z.1.1 z.1.2 z.2) := by
  simp only [blockIso_apply]
  exact ((continuous_subtype_val.comp (continuous_act.comp
      ((continuous_fst.comp continuous_fst).prodMk (V.orthogonalProjectionOnto.continuous.comp continuous_snd)))).add
    (continuous_subtype_val.comp (continuous_act.comp
      ((continuous_snd.comp continuous_fst).prodMk (Vᗮ.orthogonalProjectionOnto.continuous.comp continuous_snd)))))

@[simp] lemma blockIso_one (V : Submodule ℝ E) (x : E) : blockIso V 1 1 x = x := by
  rw [blockIso_apply,act_one,act_one]
  exact V.starProjection_add_starProjection_orthogonal x

@[simp] lemma blockIso_on_left (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) (x : V) :
    blockIso V u w (x : E) = ((act (E := V) u x : V) : E) := by
  rw [blockIso_apply,Vᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal (by simp)]
  simp [act]

@[simp] lemma blockIso_on_right (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) (x : Vᗮ) :
    blockIso V u w (x : E) = ((act (E := Vᗮ) w x : Vᗮ) : E) := by
  rw [blockIso_apply,V.orthogonalProjectionOnto_apply_of_mem_orthogonal x.prop]
  simp [act]

lemma blockIso_mul (V : Submodule ℝ E) (u u' : Orthogonal V) (w w' : Orthogonal Vᗮ) (x : E) :
    blockIso V (u*u') (w*w') x = blockIso V u w (blockIso V u' w' x) := by
  rw [blockIso_apply V u' w',map_add,blockIso_on_left,blockIso_on_right]
  rw [blockIso_apply,act_mul,act_mul]

lemma blockIso_comp (V : Submodule ℝ E) (u : Orthogonal V) (w : Orthogonal Vᗮ) :
    blockIso V u w = (blockIso V u 1).trans (blockIso V 1 w) := by
  ext x
  simpa using (blockIso_mul V 1 u w 1 x)

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
noncomputable section
universe u v w
namespace SubsphereCurrent

end SubsphereCurrent
end
end

end OAI
