import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.RecordedCount
import OAI.Analysis.CoulombRadii.Localization.Partial

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

theorem radial_append_raw_gain {J m n : ℕ} (S : Nuclei J)
    (u : H1Vector (m+n)) (hu : PartlyAntisymmetric u (coreIndexSet m n))
    (A : Set Space) (hA : PartlySupported u (outIndexSet m n) A)
    {a E : ℝ} (ha : 0<a) (y : Space) (hnuc : ∀ j, 3*a ≤ ‖S.position j-y‖)
    (hE : (E:EReal) ≤ unrestrictedFormBottom S) :
    ∃ (q k : (Fin (m+n) → Fin 2) → ℕ)
      (e : (p : Fin (m+n) → Fin 2) → Fin (q p+k p) ≃ Fin n),
      let χ := radialCut y (40*a)
      let D := radialCutCoefficient/(40*a)
      let v := fun p => u.appendCut χ (radialCut_smooth y (40*a))
        (radialCut_partition y (40*a)) D
        (div_nonneg radialCutCoefficient_pos.le (by positivity))
        (radialCut_derivative_bound y (by positivity)) p (e p)
      (∑ p, mass (v p))=mass u ∧
      (∀ p, PartlyAntisymmetric (v p) (coreIndexSet (m+q p) (k p))) ∧
      (∀ p, PartlySupported (v p) (coreIndexSet (m+q p) (k p)) {z | 40*a ≤ ‖z-y‖}) ∧
      (∀ p, PartlySupported (v p) (outIndexSet (m+q p) (k p)) (A∪Metric.closedBall y (80*a))) ∧
      (∀ W : Configuration (m+n) → ℝ, Measurable W → (∃ B : ℝ, ∀ x, |W x| ≤ B) →
        (∑ p, potentialForm (W ∘ reindexConfiguration (coreReindex m (e p)) ∘
          reindexConfiguration (recordAssoc m (q p) (k p))) (v p))=potentialForm W u) ∧
      a/(16*ballTrialCoefficient)*sliceExpectation u (fun s x =>
        (max (coreConditionalObservable u
          (rawSignedField (attraction S y) {z | 40*a ≤ ‖z-y‖} y) s x) 0)^2) ≤
        form S u+3*D^2*expectedPopulation u (Metric.closedBall y (80*a))-
          (∑ p, conditionalOutCost S (v p))-E*mass u+
          (4*ballTrialCoefficient*(screenBaseMass a)^2/a)*mass u := by
  have hr : 0<40*a := by positivity
  let χ := radialCut y (40*a)
  let D := radialCutCoefficient/(40*a)
  have hD : 0≤D := div_nonneg radialCutCoefficient_pos.le hr.le
  have hc : ∀ z∉{z : Space | 40*a ≤ ‖z-y‖}, χ 1 z=0 := by
    intro z hz
    exact radialCut_core_zero y hr z (le_of_lt (by simpa only [Set.mem_ofPred_eq,not_le] using hz))
  have ho : ∀ z∉Metric.closedBall y (80*a), χ 0 z=0 := by
    intro z hz
    apply radialCut_out_zero y hr
    have h : 80*a < ‖z-y‖ := by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hz
    linarith
  have H (p : Fin (m+n) → Fin 2) := binary_append_cut_outcome u hu hA χ
    (radialCut_smooth y (40*a)) (radialCut_partition y (40*a)) D hD
    (radialCut_derivative_bound y hr) p _ _ ho hc
  choose q k e hanti hcore hout using H
  let v := fun p : Fin (m+n) → Fin 2 => u.appendCut χ (radialCut_smooth y (40*a))
    (radialCut_partition y (40*a)) D hD (radialCut_derivative_bound y hr) p (e p)
  have hm : (∑ p, mass (v p))=mass u := by
    simp only [v,mass_appendCut]
    exact mass_labelCut u χ _ _ _ _ _
  have hs (p) (s : Spins (m+q p)) : ∀ᵐ x,
      SpatiallySupported ((v p).coreSlice s x).normalized {z | 40*a ≤ ‖z-y‖} := by
    filter_upwards [(hcore p).coreSlice s] with x hx
    exact hx.normalized
  have hconserve (W : Configuration (m+n) → ℝ) (hW : Measurable W)
      (hB : ∃ B : ℝ, ∀ x, |W x| ≤ B) :
      (∑ p, potentialForm (W ∘ reindexConfiguration (coreReindex m (e p)) ∘
        reindexConfiguration (recordAssoc m (q p) (k p))) (v p))=potentialForm W u := by
    simp only [v,potentialForm_appendCut]
    obtain ⟨B,hB⟩ := hB
    exact potentialForm_labelCut u χ _ _ _ _ _ W hW hB
  have hclosed : IsClosed {z : Space | 40*a ≤ ‖z-y‖} := isClosed_le continuous_const (by fun_prop)
  have hg (p : Fin (m+n) → Fin 2) :
      a/(16*ballTrialCoefficient)*sliceExpectation (v p) (fun s x =>
        (max (coreScreenedField S ((v p).coreSlice s x).normalized y) 0)^2) ≤
      form S (v p)-conditionalOutCost S (v p)-E*mass (v p)+
        (4*ballTrialCoefficient*(screenBaseMass a)^2/a)*mass (v p) := by
    have HG := conditional_positive_field_gain S (v p) ((hanti p).coreSlice) ha y _ hclosed
      (hs p) (fun z hz => by change 40*a ≤ ‖z-y‖ at hz; linarith) hnuc hE
    rw [form_eq_conditionalOutCost S (v p)]
    linarith
  have HI : (∑ p, form S (v p)) ≤ form S u+3*D^2*expectedPopulation u (Metric.closedBall y (80*a)) := by
    simp only [v,form_appendCut]
    have HI := form_radial_labelCut S u y hr
    have heq : 2*(40*a)=80*a := by ring
    rw [heq] at HI
    exact HI
  have HG := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hg p)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,hm] at HG
  have hraw (p) : sliceExpectation (v p) (fun s x =>
      (max (coreConditionalObservable (v p) (rawSignedField (attraction S y) {z | 40*a ≤ ‖z-y‖} y) s x) 0)^2) ≤
      sliceExpectation (v p) (fun s x => (max (coreScreenedField S ((v p).coreSlice s x).normalized y) 0)^2) := by
    apply Finset.sum_le_sum
    intro s hs0
    apply integral_mono_of_nonneg
    · exact Eventually.of_forall (fun x => mul_nonneg (mass_nonneg _) (sq_nonneg _))
    · exact coreField_positive_square_weight_integrable S (v p) s y
    · filter_upwards [hs p s] with x hx
      exact raw_posterior_positive_le_core S (v p) ha y s x hx
  let W : Configuration (m+n) → ℝ := rawSignedField (attraction S y) {z | 40*a ≤ ‖z-y‖} y
  have hW : Measurable W := rawSignedField_measurable _ hclosed.measurableSet y
  let B := |attraction S y|+((m+n:ℕ):ℝ)/(40*a)
  have hB0 : 0≤B := by dsimp [B]; positivity
  have hB : ∀ x, |W x| ≤ B := rawSignedField_abs_le _ _ y hr (fun _ h => h)
  have HJ := appendCut_positive_jensen u χ (radialCut_smooth y (40*a)) (radialCut_partition y (40*a)) D hD (radialCut_derivative_bound y hr) q k e W hW hB0 hB
  have heq (p) : W ∘ reindexConfiguration (coreReindex m (e p)) ∘ reindexConfiguration (recordAssoc m (q p) (k p))=
      rawSignedField (attraction S y) {z | 40*a ≤ ‖z-y‖} y := by
    funext x
    simp only [W,Function.comp_apply,rawSignedField_reindex]
  simp only [heq] at HJ
  have HJL := HJ.trans (Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hraw p))
  have hcoef : 0≤a/(16*ballTrialCoefficient) := div_nonneg ha.le (mul_nonneg (by norm_num) ballTrialCoefficient_pos.le)
  have HK := mul_le_mul_of_nonneg_left HJL hcoef
  refine ⟨q,k,e,hm,hanti,hcore,hout,hconserve,?_⟩
  change a/(16*ballTrialCoefficient)*sliceExpectation u (fun s x => (max (coreConditionalObservable u W s x) 0)^2) ≤ _
  linarith

end Coulomb
end

end
end

end OAI
