import OAI.Probability.DilutedSpin.TrialPhysical

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators NNReal
local instance (X : TopCat) : MeasurableSpace X := borel X
local instance (X : TopCat) : BorelSpace X := ⟨rfl⟩
variable {p r : ℕ} (M : Model p) (m : Fin r → ℝ) (hm : ∀ i,0 < m i)

noncomputable def trialSiteField {k : ℕ} (ζ : Hierarchy (r+1)) (θ : Fin k → InteractionSample p) : ℝ :=
  ∫ h,trialLog r ζ m (siteLog θ h) ∂M.field.toMeasure
noncomputable def trialSiteDisorder (ζ : Hierarchy (r+1)) (k : ℕ) : ℝ :=
  ∫ θ,trialSiteField M m ζ θ ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)

include hm in
lemma integrable_trial_site_field (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    {k : ℕ} (ζ : Hierarchy (r+1)) (θ : Fin k → InteractionSample p) :
    Integrable (fun h => trialLog r ζ m (siteLog θ h)) M.field.toMeasure := by
  apply (hh.add (integrable_const (∑ j,‖(θ j).1‖))).mono'
    (((trial_site_lipschitz r m hm ζ).continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  exact ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trial_site_bound r m hm ζ θ h)

include hm in
lemma trialSiteField_bound (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    {k : ℕ} (ζ : Hierarchy (r+1)) (θ : Fin k → InteractionSample p) :
    |trialSiteField M m ζ θ|≤(∫ h : ℝ,|h| ∂M.field.toMeasure)+∑ j,‖(θ j).1‖ := by
  have hb := norm_integral_le_of_norm_le (f := fun h => trialLog r ζ m (siteLog θ h)) (hh.add (integrable_const (∑ j,‖(θ j).1‖)))
    (ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trial_site_bound r m hm ζ θ h))
  simp only [Pi.add_apply] at hb
  simpa only [trialSiteField,Real.norm_eq_abs,integral_add hh (integrable_const _),integral_const,
    probReal_univ,one_smul] using hb

include hm in
lemma stronglyMeasurable_trialSiteField (ζ : Hierarchy (r+1)) (k : ℕ) :
    StronglyMeasurable (trialSiteField M m (k := k) ζ) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  exact ((trial_site_lipschitz (p := p) (k := k) r m hm ζ).continuous.stronglyMeasurable).integral_prod_right

include hm in
lemma trialSiteField_continuous {k : ℕ} (θ : Fin k → InteractionSample p)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    Continuous (fun ζ : Hierarchy (r+1) => trialSiteField M m ζ θ) := by
  apply continuous_of_dominated (bound := fun h : ℝ => |h|+∑ j,‖(θ j).1‖)
  · intro ζ
    exact (integrable_trial_site_field M m hm hh ζ θ).aestronglyMeasurable
  · intro ζ
    exact ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trial_site_bound r m hm ζ θ h)
  · exact hh.add (integrable_const _)
  · exact ae_of_all _ (fun h => (trialLog_continuous_bound r _ (continuous_siteLog θ h)
      (siteLog_bound θ h) m hm).1)

lemma interaction_sum_integrable (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) (k : ℕ) :
    Integrable (fun θ : Fin k → InteractionSample p => ∑ j,‖(θ j).1‖)
      (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) :=
  integrable_finsetSum _ (fun _ _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ)

lemma integral_interaction_sum (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) (k : ℕ) :
    (∫ θ : Fin k → InteractionSample p,∑ j,‖(θ j).1‖ ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) =
      k*(∫ z : InteractionSample p,‖z.1‖ ∂M.disorder.toMeasure) := by
  rw [integral_finsetSum _ (fun j _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ)]
  simp only [integral_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) hθ.aestronglyMeasurable,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

include hm in
lemma integrable_trialSiteField (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (ζ : Hierarchy (r+1)) (k : ℕ) :
    Integrable (trialSiteField M m (k := k) ζ) (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) := by
  apply ((integrable_const _).add (interaction_sum_integrable M hθ k)).mono'
    (stronglyMeasurable_trialSiteField M m hm ζ k).aestronglyMeasurable
  exact ae_of_all _ (fun θ => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trialSiteField_bound M m hm hh ζ θ)

include hm in
lemma trialSiteDisorder_bound (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (ζ : Hierarchy (r+1)) (k : ℕ) :
    |trialSiteDisorder M m ζ k|≤(∫ h : ℝ,|h| ∂M.field.toMeasure)+k*(∫ z : InteractionSample p,‖z.1‖ ∂M.disorder.toMeasure) := by
  have hb := norm_integral_le_of_norm_le (f := trialSiteField M m (k := k) ζ) ((integrable_const _).add (interaction_sum_integrable M hθ k))
    (ae_of_all _ (fun θ => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trialSiteField_bound M m hm hh ζ θ))
  simp only [Pi.add_apply] at hb
  simpa only [trialSiteDisorder,Real.norm_eq_abs,integral_add (integrable_const _) (interaction_sum_integrable M hθ k),
    integral_const,probReal_univ,one_smul,integral_interaction_sum M hθ k] using hb

include hm in
lemma trialSiteDisorder_continuous (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    Continuous (fun ζ : Hierarchy (r+1) => trialSiteDisorder M m ζ k) := by
  apply continuous_of_dominated (bound := fun θ : Fin k → InteractionSample p =>
    (∫ h : ℝ,|h| ∂M.field.toMeasure)+∑ j,‖(θ j).1‖)
  · intro ζ; exact (stronglyMeasurable_trialSiteField M m hm ζ k).aestronglyMeasurable
  · intro ζ; exact ae_of_all _ (fun θ => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trialSiteField_bound M m hm hh ζ θ)
  · exact (integrable_const _).add (interaction_sum_integrable M hθ k)
  · exact ae_of_all _ (fun θ => trialSiteField_continuous M m hm θ hh)

include hm in
lemma functional_continuous (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    Continuous (fun ζ : Hierarchy (r+1) => functional M r ζ m) := by
  have hs : Continuous (fun ζ : Hierarchy (r+1) => ∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*p)) := by
    apply continuous_of_dominated (bound := fun k : ℕ =>
      (∫ h : ℝ,|h| ∂M.field.toMeasure)+k*(∫ z : InteractionSample p,‖z.1‖ ∂M.disorder.toMeasure))
    · intro ζ; exact (measurable_of_countable _).aestronglyMeasurable
    · intro ζ; exact ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trialSiteDisorder_bound M m hm hθ hh ζ k)
    · exact (integrable_const _).add ((poisson_integrable_count _).mul_const _)
    · exact ae_of_all _ (trialSiteDisorder_continuous M m hm hθ hh)
  have he : Continuous (fun ζ : Hierarchy (r+1) => ∫ θ : InteractionSample p,
      trialLog r ζ m (fun x => Real.log (edge θ.1 x)) ∂M.disorder.toMeasure) := by
    apply continuous_of_dominated (bound := fun θ : InteractionSample p => ‖θ.1‖)
    · intro ζ
      exact (((trial_edge_lipschitz r m hm ζ).continuous.comp continuous_fst).aestronglyMeasurable)
    · intro ζ; exact ae_of_all _ (fun θ => by simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply, id_eq] using trial_edge_bound r m hm ζ θ.1)
    · exact hθ
    · exact ae_of_all _ (fun θ => (trialLog_continuous_bound r _ (continuous_log_edge θ.1) (log_edge_bound θ.1) m hm).1)
  exact (continuous_const.add hs).sub (continuous_const.mul he)

end DilutedSpinGlass

end

end OAI
