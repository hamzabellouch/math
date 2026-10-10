import OAI.Analysis.HenonEmden.CapLoss

namespace OAI

universe uE

section LayerIntegration

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LineComponents Angular

lemma low_high_layer_bound {F : ℝ → ℝ} {f w T a : ℝ}
    (hf : 0 ≤ f) (hw : 0 ≤ w) (hT : 0 ≤ T) (ha : 0 ≤ a)
    (hglobal : ∀ t ∈ Ioo 0 f, F t ≤ w)
    (hhigh : ∀ t ∈ Ioo 0 f, T ≤ t → F t ≤ a) :
    (∫⁻ t in Ioo 0 f, ENNReal.ofReal (F t)) ≤ ENNReal.ofReal (a*f+w*T) := by
  classical
  have hpt (t : ℝ) (ht : t ∈ Ioo 0 f) :
      ENNReal.ofReal (F t) ≤ ENNReal.ofReal a+(Ioo 0 T).indicator (fun _ => ENNReal.ofReal w) t := by
    by_cases hlt : t < T
    · rw [indicator_of_mem (show t ∈ Ioo 0 T from ⟨ht.1,hlt⟩)]
      exact (ENNReal.ofReal_le_ofReal (hglobal t ht)).trans (le_add_left le_rfl)
    · rw [indicator_of_notMem (fun hh => hlt hh.2),add_zero]
      exact ENNReal.ofReal_le_ofReal (hhigh t ht (not_lt.mp hlt))
  calc
    _ ≤ ∫⁻ t in Ioo 0 f, ENNReal.ofReal a+(Ioo 0 T).indicator (fun _ => ENNReal.ofReal w) t :=
      lintegral_mono_ae (ae_restrict_mem measurableSet_Ioo |>.mono hpt)
    _ = ENNReal.ofReal a*ENNReal.ofReal f+
        ∫⁻ t in Ioo 0 f, (Ioo 0 T).indicator (fun _ => ENNReal.ofReal w) t := by
      rw [lintegral_add_left measurable_const,lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo,sub_zero]
    _ ≤ ENNReal.ofReal a*ENNReal.ofReal f+
        ∫⁻ t, (Ioo 0 T).indicator (fun _ => ENNReal.ofReal w) t := by
      exact add_le_add le_rfl (lintegral_mono' Measure.restrict_le_self (le_refl _))
    _ = _ := by
      rw [lintegral_indicator measurableSet_Ioo,lintegral_const,Measure.restrict_apply_univ,
        Real.volume_Ioo,sub_zero,← ENNReal.ofReal_mul ha,← ENNReal.ofReal_mul hw,
        ← ENNReal.ofReal_add (mul_nonneg ha hf) (mul_nonneg hw hT)]

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def averagedLoss (f : E → ℝ) (κ δ : ℝ) (z : E × ℝ) : ℝ :=
  ∫ e : sphere (0:E) 1, weight μ κ e z.1-lineWeight μ f κ δ (e,z) ∂μ.toSphere

lemma measurable_averagedLoss {f : E → ℝ}
    (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (δ : ℝ) :
    Measurable (averagedLoss μ f κ δ) := by
  have hm : Measurable (fun z : sphere (0:E) 1 × (E × ℝ) =>
      weight μ κ z.1 z.2.1-lineWeight μ f κ δ z) :=
    ((measurable_weight μ hκ hκ1).comp (measurable_fst.prodMk measurable_snd.fst)).sub
      (measurable_lineWeight μ hf hκ hκ1 δ)
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

omit [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [μ.IsAddHaarMeasure] in
lemma averagedLoss_nonneg (f : E → ℝ) (κ δ : ℝ) (z : E × ℝ) :
    0 ≤ averagedLoss μ f κ δ z :=
  integral_nonneg (fun e => sub_nonneg.mpr (lineWeight_le μ f κ δ (e,z)))

lemma averagedLoss_high {f : E → ℝ}
    (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    {κ δ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    {x : E} (hd : 0 < d x) {t M P : ℝ} (ht : 0 < t) (htf : t < f x)
    (hM : 0 ≤ M) (hP : 0 < P) (hlevel : P/(d x)^(k (Module.finrank ℝ E)) ≤ t)
    (hm : (∫⁻ z in ball (0:E) 4, ENNReal.ofReal (f z) ∂μ) ≤ ENNReal.ofReal M) :
    averagedLoss μ f κ δ (x,t) ≤
      (oscillationConstant μ κ*δ*μ.toSphere.real univ+
        (boundConstant μ κ*rayConstant (Module.finrank ℝ E)*M)/δ^(Module.finrank ℝ E)/P)*
      (d x)^(N (Module.finrank ℝ E)) := by
  let n := Module.finrank ℝ E
  have hC : 0 ≤ boundConstant μ κ*rayConstant n*M :=
    mul_nonneg (mul_nonneg (boundConstant_nonneg μ hκ.le) (show 0 ≤ rayConstant n by unfold rayConstant; positivity)) hM
  have hh := high_level_flatness n hd hδ ht hP hC ((div_le_iff₀ (pow_pos hd _)).mp hlevel)
  have he := averaged_loss_le μ hf hκ hκ1 hδ hδ1 hd ht htf hM hm
  change averagedLoss μ f κ δ (x,t) ≤ _ at he
  calc
    _ ≤ oscillationConstant μ κ*δ*(d x)^(N n)*μ.toSphere.real univ+
      (boundConstant μ κ*rayConstant n*M)*(d x)^(N n-n)/(t*(δ*(d x)^(m n))^n) := by
      convert he using 1; ring
    _ ≤ oscillationConstant μ κ*δ*(d x)^(N n)*μ.toSphere.real univ+
      (boundConstant μ κ*rayConstant n*M)/δ^n/P*(d x)^(N n) := add_le_add le_rfl hh
    _ = _ := by ring

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma weight_low_levels_bound (n : ℕ) {x : E} (hd : 0 < d x) {P : ℝ} (hP : 0 ≤ P) :
    w n x*(P/(d x)^(k n)) ≤ (6*(N n:ℝ)*3^(N n-1))*P := by
  have hw : w n x ≤ 6*(N n:ℝ)*3^(N n-1)*(d x)^(N n-1) := by
    rw [w_eq_profile]; exact wProfile_bound n (norm_nonneg x)
  have hp : (d x)^(N n-1) ≤ (d x)^(k n) :=
    pow_le_pow_of_le_one hd.le (d_le_one x) (by unfold N; omega)
  calc
    _ ≤ (6*(N n:ℝ)*3^(N n-1)*(d x)^(N n-1))*(P/(d x)^(k n)) :=
      mul_le_mul_of_nonneg_right hw (div_nonneg hP (pow_nonneg hd.le _))
    _ ≤ (6*(N n:ℝ)*3^(N n-1)*(d x)^(k n))*(P/(d x)^(k n)) := by gcongr
    _ = _ := by field_simp

lemma integrated_averagedLoss {f : E → ℝ}
    (hf : IsOpen {z : E × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    {κ δ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    {x : E} (hd : 0 < d x) (hfx : 0 ≤ f x) {M P : ℝ} (hM : 0 ≤ M) (hP : 0 < P)
    (hm : (∫⁻ z in ball (0:E) 4, ENNReal.ofReal (f z) ∂μ) ≤ ENNReal.ofReal M) :
    (∫⁻ t in Ioo 0 (f x), ENNReal.ofReal (averagedLoss μ f κ δ (x,t))) ≤
      ENNReal.ofReal ((oscillationConstant μ κ*δ*μ.toSphere.real univ+
        (boundConstant μ κ*rayConstant (Module.finrank ℝ E)*M)/δ^(Module.finrank ℝ E)/P)*
        (d x)^(N (Module.finrank ℝ E))*f x + (6*(N (Module.finrank ℝ E):ℝ)*3^(N (Module.finrank ℝ E)-1))*P) := by
  let n := Module.finrank ℝ E
  apply (low_high_layer_bound hfx (w_nonneg n x) (div_nonneg hP.le (pow_nonneg hd.le _))
    (a := (oscillationConstant μ κ*δ*μ.toSphere.real univ+
      (boundConstant μ κ*rayConstant n*M)/δ^n/P)*(d x)^(N n))
    (by exact mul_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg (oscillationConstant_nonneg μ hκ.le) hδ.le) (measureReal_nonneg))
      (div_nonneg (div_nonneg (mul_nonneg (mul_nonneg (boundConstant_nonneg μ hκ.le)
        (show 0 ≤ rayConstant n by unfold rayConstant; positivity)) hM) (pow_nonneg hδ.le _)) hP.le)) (pow_nonneg hd.le _))
    (fun t _ => averaged_loss_le_weight μ hf hκ hκ1 δ x t)
    (fun t ht hlevel => averagedLoss_high μ hf hκ hκ1 hδ hδ1 hd ht.1 ht.2 hM hP hlevel hm)).trans
  apply ENNReal.ofReal_le_ofReal
  exact add_le_add le_rfl (weight_low_levels_bound n hd hP.le)

end HenonLaneEmden.SpatialComponents
end
end LayerIntegration

end OAI
