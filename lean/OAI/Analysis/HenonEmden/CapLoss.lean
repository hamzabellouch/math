import OAI.Analysis.HenonEmden.AngularIntegration

namespace OAI

universe uE

section CapLoss

open MeasureTheory Set Metric
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LineComponents Angular
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma length_at {f : E → ℝ} (x : E) {t : ℝ} (ht : 0 < t) (e : sphere (0:E) 1) :
    componentLength (lineLayer f) (e,x,t) =
      componentLength {z : sphere (0:E) 1 × ℝ | t < f (x+z.2 • z.1.1)} e := by
  classical
  have hs (r : ℝ) : SegmentInside (lineLayer f) (e,x,t) r ↔
      SegmentInside {z : sphere (0:E) 1 × ℝ | t < f (x+z.2 • z.1.1)} e r := by
    change (∀ s ∈ uIcc 0 r, 0 < t ∧ t < f (x+s • e.1)) ↔
      (∀ s ∈ uIcc 0 r, t < f (x+s • e.1))
    simp only [ht,true_and]
  unfold componentLength forwardExit backwardExit
  congr 1 <;> apply iSup_congr <;> intro r
  · exact if_congr (hs (r : ℝ)) rfl rfl
  · exact if_congr (hs (-(r : ℝ))) rfl rfl

lemma integrable_loss {f : E → ℝ} (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (δ : ℝ) (x : E) (t : ℝ) :
    Integrable (fun e : sphere (0:E) 1 => weight μ κ e x-lineWeight μ f κ δ (e,x,t)) μ.toSphere := by
  have hm := (continuous_weight_direction μ κ x).measurable.sub
    ((measurable_lineWeight μ hf hκ hκ1 δ).comp (show Measurable (fun e : sphere (0:E) 1 => (e,x,t)) by fun_prop))
  apply (integrable_const (boundConstant μ κ)).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro e
  change ‖weight μ κ e x-lineWeight μ f κ δ (e,x,t)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (lineWeight_le μ f κ δ (e,x,t)))]
  exact (sub_le_self _ (lineWeight_nonneg μ f κ δ _)).trans (weight_le_constant μ hκ hκ1 e x)

lemma averaged_loss_le_weight {f : E → ℝ} (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (δ : ℝ) (x : E) (t : ℝ) :
    (∫ e, weight μ κ e x-lineWeight μ f κ δ (e,x,t) ∂μ.toSphere) ≤ w (Module.finrank ℝ E) x := by
  have hi : Integrable (fun e : sphere (0:E) 1 => weight μ κ e x) μ.toSphere :=
    (integrable_const (boundConstant μ κ)).mono' (continuous_weight_direction μ κ x).aestronglyMeasurable
      (ae_of_all _ (fun e => by rw [Real.norm_eq_abs,abs_of_nonneg (weight_nonneg μ _ _ _)]; exact weight_le_constant μ hκ hκ1 e x))
  rw [← integral_weight μ hκ hκ1 x]
  exact integral_mono (integrable_loss μ hf hκ hκ1 δ x t) hi
    (fun e => sub_le_self _ (lineWeight_nonneg μ f κ δ _))

lemma averaged_loss_le {f : E → ℝ} (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    {κ δ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    {x : E} (hd : 0 < d x) {t M : ℝ} (ht : 0 < t) (htf : t < f x) (hM : 0 ≤ M)
    (hm : (∫⁻ z in ball (0:E) 4, ENNReal.ofReal (f z) ∂μ) ≤ ENNReal.ofReal M) :
    (∫ e, weight μ κ e x-lineWeight μ f κ δ (e,x,t) ∂μ.toSphere) ≤
      oscillationConstant μ κ*δ*(d x)^(N (Module.finrank ℝ E))*μ.toSphere.real univ +
      (boundConstant μ κ*(d x)^(N (Module.finrank ℝ E)-Module.finrank ℝ E))*
        (rayConstant (Module.finrank ℝ E)*M/(t*(δ*(d x)^(m (Module.finrank ℝ E)))^(Module.finrank ℝ E))) := by
  let l := δ*(d x)^(m (Module.finrank ℝ E))
  let U := {z : sphere (0:E) 1 × ℝ | t < f (x+z.2 • z.1.1)}
  let S := {e | ENNReal.ofReal l < componentLength U e}
  have hU : IsOpen U := by
    have hh := hf.preimage (show Continuous (fun z : sphere (0:E) 1 × ℝ => (x+z.2 • z.1.1,t)) by fun_prop)
    simpa only [preimage_ofPred_eq,ht,true_and] using hh
  have hS : MeasurableSet S := measurableSet_lt measurable_const (measurable_componentLength hU)
  have hF := (continuous_weight_direction μ κ x).measurable.sub
    ((measurable_lineWeight μ hf hκ hκ1 δ).comp (show Measurable (fun e : sphere (0:E) 1 => (e,x,t)) by fun_prop))
  have hb : 0 ≤ boundConstant μ κ*(d x)^(N (Module.finrank ℝ E)-Module.finrank ℝ E) :=
    mul_nonneg (boundConstant_nonneg μ hκ.le) (pow_nonneg hd.le _)
  have he := integral_le_constant_add_event μ.toSphere hS hF
    (a := oscillationConstant μ κ*δ*(d x)^(N (Module.finrank ℝ E)))
    (H := boundConstant μ κ*(d x)^(N (Module.finrank ℝ E)-Module.finrank ℝ E))
    (mul_nonneg (mul_nonneg (oscillationConstant_nonneg μ hκ.le) hδ.le) (pow_nonneg hd.le _)) hb
    (fun e => sub_nonneg.mpr (lineWeight_le μ f κ δ (e,x,t)))
    (fun e => (sub_le_self _ (lineWeight_nonneg μ f κ δ _)).trans (weight_bound μ hκ hκ1 e x))
    (by
      intro e he
      apply short_loss μ hf hκ hκ1 hδ.le hδ1 e hd ht htf
      rw [length_at x ht]
      exact le_of_not_gt he)
  have hl : 0 < l := mul_pos hδ (pow_pos hd _)
  have hl1 : l ≤ 1 := (mul_le_of_le_one_left (pow_nonneg hd.le _)
    (by linarith : δ ≤ 1)).trans (pow_le_one₀ hd.le (d_le_one x))
  have hp := long_component_measure_le μ ((d_pos_iff x).mp hd).le ht hl hl1 hM hU hm
  apply he.trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hb)

lemma high_level_flatness (n : ℕ) {D δ t P C : ℝ} (hD : 0 < D) (hδ : 0 < δ)
    (ht : 0 < t) (hP : 0 < P) (hC : 0 ≤ C) (hlevel : P ≤ t*D^(k n)) :
    C*D^(N n-n)/(t*(δ*D^(m n))^n) ≤ C/δ^n/P*D^(N n) := by
  have hn : (N n-n)+k n = N n+m n*n := by
    simp only [N,k,m,Nat.mul_add,Nat.add_mul]
    omega
  have hp : D^(N n-n)*D^(k n) = D^(N n)*D^(m n*n) := by rw [← pow_add,← pow_add,hn]
  have he : C*D^(N n-n)/(t*(δ*D^(m n))^n) = (C/δ^n)*(D^(N n)/(t*D^(k n))) := by
    rw [mul_pow,← pow_mul]
    field_simp
    nlinarith [congrArg (fun r => C*δ^n*t*r) hp]
  rw [he]
  calc
    _ ≤ (C/δ^n)*(D^(N n)/P) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (pow_nonneg hD.le _) hP hlevel) (div_nonneg hC (pow_nonneg hδ.le _))
    _ = _ := by ring

end HenonLaneEmden.SpatialComponents
end
end CapLoss

end OAI
