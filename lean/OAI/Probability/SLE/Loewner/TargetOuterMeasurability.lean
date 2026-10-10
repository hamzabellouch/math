import OAI.Probability.SLE.Angle.TargetLevelMeasurability
import OAI.Probability.SLE.Angle.TargetAngleLaw

namespace OAI

/-! Measurability for the outer angle integral in the prescribed moments.
The exact potential is extended by zero only outside the support of the
angle law; the original coefficient functions agree almost everywhere. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped NNReal ENNReal

namespace SLEExactGauge.Target

lemma measurable_potentialDifference_restricted_angle
    (κ : ℝ) (W : WienerLaw) [SFinite W] (h i : ℕ) :
    Measurable (fun p : ℝ × Driver => if p.1 ∈ Ioo (0:ℝ) Real.pi then
      potentialDifference κ p.1 W p.2 h i else 0) := by
  classical
  let t : ℝ≥0 := NNReal.mk ((i:ℝ)*mesh h)
    (mul_nonneg (Nat.cast_nonneg i) (mesh_pos h).le)
  let T : ℝ≥0 := NNReal.mk (((i:ℝ)+1)*mesh h)
    (mul_nonneg (by positivity) (mesh_pos h).le)
  let v (p : ℝ × Driver) : ℝ≥0∞ :=
    if p.1 ∈ Ioo (0:ℝ) Real.pi then potential κ p.1 p.2 t else 0
  let w (p : ℝ × Driver) : ℝ≥0∞ := ∫⁻ c,
    if p.1 ∈ Ioo (0:ℝ) Real.pi then potential κ p.1 (concat p.2 c t) T else 0 ∂W
  have hv : Measurable v :=
    (measurable_potential_restricted_angle κ).comp (measurable_const.prodMk measurable_id)
  have hc : Measurable (fun p : (ℝ × Driver) × Driver => concat p.1.2 p.2 t) :=
    measurable_concat.comp
      (measurable_const.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hp : Measurable (fun p : (ℝ × Driver) × Driver =>
      (T,(p.1.1,concat p.1.2 p.2 t))) :=
    measurable_const.prodMk (measurable_fst.fst.prodMk hc)
  have hw : Measurable w :=
    ((measurable_potential_restricted_angle κ).comp hp).lintegral_prod_right'
  have hm : Measurable (fun p : ℝ × Driver =>
      if v p < ∞ ∧ w p < ∞ then (v p).toReal-(w p).toReal else (0:ℝ)) :=
    (hv.ennreal_toReal.sub hw.ennreal_toReal).ite
    ((measurableSet_lt hv measurable_const).inter (measurableSet_lt hw measurable_const))
      measurable_const
  convert hm using 1
  funext p
  by_cases hθ : p.1 ∈ Ioo (0:ℝ) Real.pi
  · have hθ' : 0 < p.1 ∧ p.1 < Real.pi := hθ
    simp [v,w,potentialDifference,hθ,hθ',t,T]
  · have hθ' : ¬ (0 < p.1 ∧ p.1 < Real.pi) := hθ
    simp [v,w,hθ,hθ',t,T]

lemma measurable_discreteMass_restricted_angle
    (κ ℓ : ℝ) (W : WienerLaw) [SFinite W] (h : ℕ) :
    Measurable (fun p : ℝ × Driver => if p.1 ∈ Ioo (0:ℝ) Real.pi then
      discreteMass κ p.1 W p.2 ℓ h else 0) := by
  have hm : Measurable (fun p : ℝ × Driver => ∑ i ∈ Finset.range (h*2^h),
      if ENNReal.ofReal (((i:ℝ)+1)*mesh h) ≤ levelTime κ p.1 p.2 ℓ
      then (if p.1 ∈ Ioo (0:ℝ) Real.pi then potentialDifference κ p.1 W p.2 h i else 0)
      else 0) := by
    apply Finset.measurable_sum
    intro i _
    exact (measurable_potentialDifference_restricted_angle κ W h i).ite
      (measurableSet_le measurable_const (measurable_levelTime_angle κ ℓ)) measurable_const
  convert hm using 1
  funext p
  by_cases hθ : p.1 ∈ Ioo (0:ℝ) Real.pi
  · simp only [ite_eq_left hθ,discreteMass]
  · simp only [ite_eq_right hθ,ite_self,Finset.sum_const_zero]

lemma angleLaw_prod_ae_mem (κ : ℝ) (W : WienerLaw) [SFinite W] :
    ∀ᵐ p ∂(angleLaw κ).prod W, p.1 ∈ Ioo (0:ℝ) Real.pi := by
  apply (Measure.ae_prod_iff_ae_ae (measurable_fst measurableSet_Ioo)).2
  filter_upwards [angleLaw_ae_mem κ] with θ hθ
  exact ae_of_all _ (fun _ => hθ)

lemma aemeasurable_potential_angle (κ : ℝ) (W : WienerLaw) [SFinite W] (t : ℝ≥0) :
    AEMeasurable (fun p : ℝ × Driver => potential κ p.1 p.2 t) ((angleLaw κ).prod W) := by
  have hm : AEMeasurable (fun p : ℝ × Driver =>
      if p.1 ∈ Ioo (0:ℝ) Real.pi then potential κ p.1 p.2 t else 0)
      ((angleLaw κ).prod W) :=
    ((measurable_potential_restricted_angle κ).comp
      ((measurable_const : Measurable (fun _ : ℝ × Driver => t)).prodMk measurable_id)).aemeasurable
  apply hm.congr
  filter_upwards [angleLaw_prod_ae_mem κ W] with p hp
  exact ite_eq_left hp

lemma aemeasurable_discreteMass_angle
    (κ ℓ : ℝ) (W : WienerLaw) [SFinite W] (h : ℕ) :
    AEMeasurable (fun p : ℝ × Driver => discreteMass κ p.1 W p.2 ℓ h)
      ((angleLaw κ).prod W) := by
  apply (measurable_discreteMass_restricted_angle κ ℓ W h).aemeasurable.congr
  filter_upwards [angleLaw_prod_ae_mem κ W] with p hp
  exact ite_eq_left hp

lemma aemeasurable_coefficient_integrand
    (κ ℓ u : ℝ) (W : WienerLaw) [SFinite W] (h k : ℕ) :
    AEMeasurable (fun p : ℝ × Driver => levelDensity κ p.1 p.2 ℓ *
      (clip u (discreteMass κ p.1 W p.2 ℓ h))^k) ((angleLaw κ).prod W) := by
  have hc : Continuous (fun x : ℝ => (clip u x)^k) := by
    unfold clip
    fun_prop
  exact (measurable_levelDensity_angle κ ℓ).aemeasurable.mul
    (hc.measurable.comp_aemeasurable (aemeasurable_discreteMass_angle κ ℓ W h))

end SLEExactGauge.Target

end

end OAI
