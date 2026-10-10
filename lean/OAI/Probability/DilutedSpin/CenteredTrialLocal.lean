import OAI.Probability.DilutedSpin.CenteredPressure
import OAI.Probability.DilutedSpin.PressureLiminf
import OAI.Probability.DilutedSpin.RealEncoding

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

lemma logWeightedExp_add_constant {ι : Type*} [Fintype ι] [Nonempty ι]
    (f w : ι → ℝ) (hw : ∀ i,0 < w i) (a : ℝ) :
    Real.log (∑ i,Real.exp (f i+a)*w i)=Real.log (∑ i,Real.exp (f i)*w i)+a := by
  have he : (∑ i,Real.exp (f i+a)*w i)=(∑ i,Real.exp (f i)*w i)*Real.exp a := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.exp_add]
    ring
  rw [he,Real.log_mul (ne_of_gt (Finset.sum_pos (fun i _ => mul_pos (Real.exp_pos _) (hw i)) Finset.univ_nonempty))
    (Real.exp_ne_zero _),Real.log_exp]

lemma log_edge_center {p : ℕ} (z : InteractionSample p) (x : Fin p → ℝ) :
    Real.log (edge (centerSample z).1 x)=Real.log (edge z.1 x)-referenceEnergy z := by
  simpa only [edge,centerSample,centeredInteraction,referenceEnergy,sub_eq_add_neg] using
    logWeightedExp_add_constant z.1 (fun s => ∏ l,q (x l) (s l))
      (fun s => Finset.prod_pos (fun l _ => q_pos _ _)) (-referenceEnergy z)

lemma message_center {p : ℕ} (z : InteractionSample p) (x : Fin (p-1) → ℝ) (ε : Spin) :
    message (centerSample z).1 x ε=message z.1 x ε-referenceEnergy z := by
  simpa only [message,centerSample,centeredInteraction,referenceEnergy,sub_eq_add_neg] using
    logWeightedExp_add_constant (fun s => z.1 (appendSpin s ε)) (fun s => ∏ l,q (x l) (s l))
      (fun s => Finset.prod_pos (fun l _ => q_pos _ _)) (-referenceEnergy z)

lemma siteLog_center {p k : ℕ} (θ : Fin k → InteractionSample p) (h : ℝ)
    (x : Fin k×Fin (p-1) → ℝ) :
    siteLog (fun j => centerSample (θ j)) h x=siteLog θ h x-(∑ j,referenceEnergy (θ j)) := by
  have he ε : h*spin ε+∑ j,message (centerSample (θ j)).1 (fun l => x (j,l)) ε=
      (h*spin ε+∑ j,message (θ j).1 (fun l => x (j,l)) ε)+(-(∑ j,referenceEnergy (θ j))) := by
    simp only [message_center,Finset.sum_sub_distrib]
    ring
  simp only [siteLog,he]
  have hh := logWeightedExp_add_constant (fun ε => h*spin ε+∑ j,message (θ j).1 (fun l => x (j,l)) ε)
    (fun _ : Spin => (1:ℝ)/2) (fun _ => by norm_num) (-(∑ j,referenceEnergy (θ j)))
  simpa only [mul_one_div,← Finset.sum_div,sub_eq_add_neg] using hh

lemma trial_site_center {p k r : ℕ} (θ : Fin k → InteractionSample p) (h : ℝ)
    (m : Fin r → ℝ) (hm : ∀ i,0 < m i) (ζ : Hierarchy (r+1)) :
    trialLog r ζ m (siteLog (fun j => centerSample (θ j)) h)=
      trialLog r ζ m (siteLog θ h)-(∑ j,referenceEnergy (θ j)) := by
  have he : siteLog (fun j => centerSample (θ j)) h=(fun x => siteLog θ h x+(-(∑ j,referenceEnergy (θ j)))) := by
    funext x
    simpa only [sub_eq_add_neg] using siteLog_center θ h x
  rw [he,trialLog_add_constant r _ (continuous_siteLog θ h) (siteLog_bound θ h) m hm]
  rfl

lemma trial_edge_center {p r : ℕ} (z : InteractionSample p)
    (m : Fin r → ℝ) (hm : ∀ i,0 < m i) (ζ : Hierarchy (r+1)) :
    trialLog r ζ m (fun x => Real.log (edge (centerSample z).1 x))=
      trialLog r ζ m (fun x => Real.log (edge z.1 x))-referenceEnergy z := by
  simp_rw [log_edge_center,sub_eq_add_neg]
  rw [trialLog_add_constant r _ (continuous_log_edge z.1) (log_edge_bound z.1) m hm]
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter

lemma centeredModel_interaction_integrable {p : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) :
    Integrable (fun z : InteractionSample p => ‖z.1‖) (centeredModel M).disorder.toMeasure := by
  exact mapModel_interaction_integrable M centerSample id (measurable_centerSample p) measurable_id
    (centeredInteraction_integrable M hθ)

lemma centeredModel_field_integrable {p : ℕ} (M : Model p)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    Integrable (fun h : ℝ => |h|) (centeredModel M).field.toMeasure := by
  exact mapModel_field_integrable M centerSample id (measurable_centerSample p) measurable_id hh

lemma liminf_pressure_center {p : ℕ} (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    liminf (pressure (centeredModel M)) atTop=liminf (pressure M) atTop-
      (M.alpha:ℝ)*(∫ z,referenceEnergy z ∂M.disorder.toMeasure) := by
  have he : pressure (centeredModel M)=ᶠ[atTop]
      (fun N => pressure M N-(M.alpha:ℝ)*(∫ z,referenceEnergy z ∂M.disorder.toMeasure)) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact pressure_center M hN hθ hh
  rw [liminf_congr he]
  exact liminf_sub_const atTop (pressure M) _ (pressure_bounded M hθ hh).1.isCobounded_ge
    (pressure_bounded M hθ hh).2
end DilutedSpinGlass

end

end OAI
