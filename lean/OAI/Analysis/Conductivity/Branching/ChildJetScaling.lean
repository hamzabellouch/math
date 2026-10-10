import Mathlib
import OAI.Analysis.Conductivity.Sobolev.ChildH1Pullback

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

lemma sourceChildEuclidean_map_volume (σ : ℝ) :
    Measure.map (sourceChildEuclidean σ) volume=ENNReal.ofReal ((sourceScale^3)⁻¹) • volume := by
  change Measure.map (((WithLp.toLp 2 : Coord3 → R3) ∘ sourceChildCoordinates σ) ∘
    (WithLp.ofLp : R3 → Coord3)) volume=_
  rw [←Measure.map_map ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
    (sourceChildCoordinates_contDiff σ).continuous.measurable)
    (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).measurable,
    (PiLp.volume_preserving_ofLp (Fin 3)).map_eq,
    ←Measure.map_map (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable
      (sourceChildCoordinates_contDiff σ).continuous.measurable,
    sourceChildCoordinates_map_volume,
    Measure.map_smul _ (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.aemeasurable,
    (PiLp.volume_preserving_toLp (Fin 3)).map_eq]

lemma sourceChildEuclidean_inverse_map_volume (σ : ℝ) :
    Measure.map (sourceChildEuclidean σ).symm volume=ENNReal.ofReal (sourceScale^3) • volume := by
  apply (sourceChildEuclidean σ).toMeasurableEquiv.measurableEmbedding.map_injective
  change Measure.map (sourceChildEuclidean σ) (Measure.map (sourceChildEuclidean σ).symm volume)=
    Measure.map (sourceChildEuclidean σ) (ENNReal.ofReal (sourceScale^3) • volume)
  rw [Measure.map_map (sourceChildEuclidean σ).measurable (sourceChildEuclidean σ).symm.measurable]
  have he : (sourceChildEuclidean σ) ∘ (sourceChildEuclidean σ).symm=id :=
    funext (sourceChildEuclidean σ).apply_symm_apply
  rw [he,Measure.map_id,Measure.map_smul _ (sourceChildEuclidean σ).measurable.aemeasurable,
    sourceChildEuclidean_map_volume,smul_smul,
    ←ENNReal.ofReal_mul (by norm_num [sourceScale])]
  norm_num [sourceScale]

lemma integral_sourceChild_inverse (σ : ℝ) (f : R3 → ℝ) :
    (∫ x,f ((sourceChildEuclidean σ).symm x))=sourceScale^3*(∫ x,f x) := by
  have hh := integral_map_equiv (μ:=(volume : Measure R3)) (sourceChildEuclidean σ).symm.toMeasurableEquiv f
  change (∫ x,f x ∂Measure.map (sourceChildEuclidean σ).symm volume)=_ at hh
  rw [sourceChildEuclidean_inverse_map_volume,integral_smul_measure,ENNReal.toReal_ofReal (by norm_num [sourceScale]),smul_eq_mul] at hh
  exact hh.symm

def childAxisSwap (v : R3) : R3 := WithLp.toLp 2 (fun i => v (childAxis i))

lemma childAxisSwap_zero : childAxisSwap 0=0 := rfl
lemma childAxisSwap_inner (v w : R3) : inner ℝ (childAxisSwap v) w=inner ℝ v (childAxisSwap w) := by
  simp only [PiLp.inner_apply,Fin.sum_univ_succ]
  simp [childAxisSwap,childAxis,RCLike.inner_apply]
  ring

lemma childAxisSwap_involutive (v : R3) : childAxisSwap (childAxisSwap v)=v := by
  ext i
  exact congrArg v (childAxis_involutive i)

lemma childAxisSwap_inner_self (v : R3) : inner ℝ (childAxisSwap v) (childAxisSwap v)=inner ℝ v v := by
  rw [childAxisSwap_inner,childAxisSwap_involutive]

lemma childH1Pullback_value (k : Fin 2) (u : H1) :
    weakValue (childH1Pullback k u)=ᵐ[ballMeasure]
      (fun x => weakValue u (sourceChildEuclidean (actualChildSign k) x)) := by
  filter_upwards [childPullbackJetCLM_ae k u.val] with x hx
  change jetValue (childPullbackJetCLM k u.val x)=_
  rw [hx]
  rfl

lemma childH1Pullback_gradient (k : Fin 2) (u : H1) :
    weakGradient (childH1Pullback k u)=ᵐ[ballMeasure]
      (fun x => sourceScale • childAxisSwap (weakGradient u (sourceChildEuclidean (actualChildSign k) x))) := by
  filter_upwards [childPullbackJetCLM_ae k u.val] with x hx
  change jetGradient (childPullbackJetCLM k u.val x)=_
  rw [hx]
  rfl

lemma childH10Transport_jet (k : Fin 2) (u : H10) :
    (childH10Transport k u).val=ᵐ[ballMeasure] fun x =>
      if (sourceChildEuclidean (actualChildSign k)).symm x∈ball then
        WithLp.toLp 2 (Fin.cases (weakValue u.val ((sourceChildEuclidean (actualChildSign k)).symm x))
          (fun j => sourceScale⁻¹*weakGradient u.val ((sourceChildEuclidean (actualChildSign k)).symm x) (childAxis j)))
      else 0 := by
  have he := ballWholePiJetCLM_ae_of_ae u.val.val (fun y => u.val.val (WithLp.toLp 2 y))
    (by filter_upwards [] with x; rfl)
  apply (childTransportJetCLM_ae_of_ae k u.val.val _ he).trans
  exact Eventually.of_forall (fun x => by
    change (WithLp.toLp 2 (Fin.cases
      ((if (sourceChildEuclidean (actualChildSign k)).symm x∈ball then u.val.val ((sourceChildEuclidean (actualChildSign k)).symm x) else 0) 0)
      (fun j => sourceScale⁻¹*(if (sourceChildEuclidean (actualChildSign k)).symm x∈ball then
        u.val.val ((sourceChildEuclidean (actualChildSign k)).symm x) else 0) (childAxis j).succ)) : JetFiber)=_
    dsimp only
    split_ifs with h
    · rfl
    · ext i
      cases i using Fin.cases <;> simp)

lemma childH10Transport_value (k : Fin 2) (u : H10) :
    weakValue (childH10Transport k u)=ᵐ[ballMeasure] fun x =>
      if (sourceChildEuclidean (actualChildSign k)).symm x∈ball then
        weakValue u.val ((sourceChildEuclidean (actualChildSign k)).symm x) else 0 := by
  filter_upwards [childH10Transport_jet k u] with x hx
  change jetValue ((childH10Transport k u).val x)=_
  rw [hx]
  split_ifs <;> rfl

lemma childH10Transport_gradient (k : Fin 2) (u : H10) :
    weakGradient (childH10Transport k u)=ᵐ[ballMeasure] fun x =>
      if (sourceChildEuclidean (actualChildSign k)).symm x∈ball then
        sourceScale⁻¹ • childAxisSwap (weakGradient u.val ((sourceChildEuclidean (actualChildSign k)).symm x)) else 0 := by
  filter_upwards [childH10Transport_jet k u] with x hx
  change jetGradient ((childH10Transport k u).val x)=_
  rw [hx]
  split_ifs <;> rfl

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

lemma integral_child_ball (k : Fin 2) (f : R3 → ℝ)
    (hf : ∀ᵐ x∂ballMeasure,(sourceChildEuclidean (actualChildSign k)).symm x∉ball → f x=0) :
    (∫ x,f x ∂ballMeasure)=sourceScale^3*(∫ x,f (sourceChildEuclidean (actualChildSign k) x) ∂ballMeasure) := by
  let S := sourceChildEuclidean (actualChildSign k)
  have hid : (fun x => if S.symm x∈ball then f x else 0)=
      (fun x => (ball.indicator (fun y => f (S y))) (S.symm x)) := by
    funext x
    simp only [indicator,Homeomorph.apply_symm_apply]
  calc
    _ = ∫ x,(if S.symm x∈ball then f x else 0) ∂ballMeasure := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      split_ifs with hb
      · rfl
      · exact hx hb
    _ = ∫ x,(if S.symm x∈ball then f x else 0) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      apply ite_eq_right
      intro hh
      apply hx
      exact sourceChildEuclidean_ball k ⟨S.symm x,hh,S.apply_symm_apply x⟩
    _ = sourceScale^3*(∫ x,ball.indicator (fun y => f (S y)) x) := by
      rw [hid]
      exact integral_sourceChild_inverse _ _
    _ = _ := by rw [integral_indicator (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)]; rfl

lemma childH10Transport_gradient_at_child (k : Fin 2) (v : H10) :
    (fun x => weakGradient (childH10Transport k v) (sourceChildEuclidean (actualChildSign k) x))=ᵐ[ballMeasure]
      (fun x => sourceScale⁻¹ • childAxisSwap (weakGradient v.val x)) := by
  filter_upwards [(sourceChildEuclidean_ball_quasi k).ae_eq_comp (childH10Transport_gradient k v),
    ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxb
  simpa only [Function.comp_apply,Homeomorph.symm_apply_apply,ite_eq_left hxb] using hx

lemma child_energy_scaling (k : Fin 2) (v : H10) (h : H1) (a : R3 → ℝ) :
    (∫ x,a x*inner ℝ (weakGradient (childH10Transport k v) x) (weakGradient h x) ∂ballMeasure)=
      sourceScale*(∫ x,a (sourceChildEuclidean (actualChildSign k) x)*
        inner ℝ (weakGradient v.val x) (weakGradient (childH1Pullback k h) x) ∂ballMeasure) := by
  rw [integral_child_ball k _ (by
    filter_upwards [childH10Transport_gradient k v] with x hx hn
    rw [hx,ite_eq_right hn,inner_zero_left,mul_zero])]
  rw [←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [childH10Transport_gradient_at_child k v,childH1Pullback_gradient k h] with x hv hh
  rw [hv,hh,real_inner_smul_left,real_inner_smul_right,childAxisSwap_inner]
  norm_num [sourceScale]
  ring

lemma weakGradient_norm_sq_integral (u : H1) :
    ‖weakGradientL u‖^2=(∫ x,inner ℝ (weakGradient u x) (weakGradient u x) ∂ballMeasure) := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weakGradientL_apply_ae u] with x hx
  rw [hx]

lemma child_gradient_norm_sq (k : Fin 2) (v : H10) :
    ‖weakGradientL (childH10Transport k v)‖^2=sourceScale*‖weakGradientL v.val‖^2 := by
  rw [weakGradient_norm_sq_integral,weakGradient_norm_sq_integral]
  rw [integral_child_ball k _ (by
    filter_upwards [childH10Transport_gradient k v] with x hx hn
    rw [hx,ite_eq_right hn,inner_zero_left])]
  rw [←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [childH10Transport_gradient_at_child k v] with x hv
  rw [hv,real_inner_smul_left,real_inner_smul_right,childAxisSwap_inner_self]
  norm_num [sourceScale]
  ring

end ScalarConductivity

end

end OAI
