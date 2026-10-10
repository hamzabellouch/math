import Mathlib
import OAI.Analysis.CoulombRadii.Screening.CoveredOutCost
import OAI.Analysis.CoulombRadii.FieldAnalysis.SortedObservable

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma localCount_join {m k : ℕ} (A : Set Space) (x : Configuration m) (v : Configuration k) :
    localCount A (joinConfiguration m k (x,v))=localCount A x+localCount A v := by
  simp only [localCount,Fin.sum_univ_add,position_join_left,position_join_right]

lemma localCount_permute {n : ℕ} (A : Set Space) (p : Equiv.Perm (Fin n)) (x : Configuration n) :
    localCount A (permute p x)=localCount A x := by
  simp only [localCount,position_permute]
  exact Equiv.sum_comp p (fun i : Fin n => A.indicator (fun _ => (1:ℝ)) (position x i))

lemma localCount_reindex {m n : ℕ} (A : Set Space) (e : Fin m ≃ Fin n) (x : Configuration m) :
    localCount A (reindexConfiguration e x)=localCount A x := by
  change (∑ i : Fin n, A.indicator (fun _ => (1:ℝ)) (position x (e.symm i)))=_
  exact Equiv.sum_comp e.symm (fun i : Fin m => A.indicator (fun _ => (1:ℝ)) (position x i))

lemma potentialForm_mono_bounded {n : ℕ} (u : H1Vector n)
    (F G : Configuration n → ℝ) (hF : Measurable F) (hG : Measurable G)
    {B C : ℝ} (hFB : ∀ x, |F x| ≤ B) (hGC : ∀ x, |G x| ≤ C)
    (hFG : ∀ x, F x ≤ G x) : potentialForm F u ≤ potentialForm G u := by
  apply Finset.sum_le_sum
  intro s hs
  apply integral_mono (boundedObservable_integrable u F hF hFB s) (boundedObservable_integrable u G hG hGC s)
  intro x
  exact mul_le_mul_of_nonneg_right (hFG x) (sq_nonneg _)

lemma sliceExpectation_localCount_sq_le {m k : ℕ} (u : H1Vector (m+k))
    {A : Set Space} (hA : MeasurableSet A) :
    sliceExpectation u (fun _ x => (localCount A x)^2) ≤ localCountSecondMoment u A := by
  let W : Configuration (m+k) → ℝ := fun v => (localCount A v)^2
  have hW : Measurable W := (localCount_measurable hA).pow_const 2
  have hB : ∀ v, |W v| ≤ ((m+k:ℕ):ℝ)^2 := by
    intro v
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (localCount_nonneg _ _) (localCount_le _ _) 2
  have hp : sliceExpectation u (fun _ x => (localCount A x)^2) ≤ sliceExpectation u (coreConditionalObservable u W) := by
    apply Finset.sum_le_sum
    intro s hs
    apply integral_mono (sliceCount_weight_integrable u hA s 2)
      (coreConditionalObservable_weight_integrable u W hW (sq_nonneg _) hB s)
    intro x
    by_cases hm : mass (u.coreSlice s x)=0
    · simp only [hm,zero_mul,le_refl]
    · apply mul_le_mul_of_nonneg_left _ (mass_nonneg _)
      have hm' := lt_of_le_of_ne (mass_nonneg (u.coreSlice s x)) (Ne.symm hm)
      let w := (u.coreSlice s x).normalized
      calc
        (localCount A x)^2 = potentialForm (fun _ : Configuration k => (localCount A x)^2) w := by
          rw [potentialForm_const,mass_normalized _ hm',mul_one]
        _ ≤ potentialForm (fun v => W (joinConfiguration m k (x,v))) w := by
          apply potentialForm_mono_bounded w _ _ measurable_const
            (hW.comp ((joinConfiguration m k).continuous.measurable.comp (measurable_const.prodMk measurable_id)))
            (fun _ => le_rfl) (fun v => hB _)
          intro v
          dsimp [W]
          rw [localCount_join]
          exact pow_le_pow_left₀ (localCount_nonneg _ _) (le_add_of_nonneg_right (localCount_nonneg _ _)) 2
        _ = _ := rfl
  rw [sliceExpectation_coreConditionalObservable u W hW hB] at hp
  exact hp

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma raw_posterior_positive_le_core {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) {a : ℝ} (ha : 0<a) (y : Space)
    (s : Spins m) (x : Configuration m)
    (hs : SpatiallySupported (u.coreSlice s x).normalized {z | 40*a ≤ ‖z-y‖}) :
    mass (u.coreSlice s x)*(max (coreConditionalObservable u
      (rawSignedField (attraction S y) {z | 40*a ≤ ‖z-y‖} y) s x) 0)^2 ≤
    mass (u.coreSlice s x)*(max (coreScreenedField S (u.coreSlice s x).normalized y) 0)^2 := by
  rw [coreConditionalObservable_raw_positive_weight u _
    (isClosed_le continuous_const (by fun_prop) : IsClosed {z : Space | 40*a ≤ ‖z-y‖}).measurableSet y (by positivity : 0<40*a) (fun _ h => h),
    restrictedCorePotential_eq _ hs]
  apply mul_le_mul_of_nonneg_left _ (mass_nonneg _)
  apply pow_le_pow_left₀ (le_max_right _ _) _ 2
  apply max_le_max _ le_rfl
  unfold coreScreenedField
  linarith [restrictedOutPotential_nonneg x {z | 40*a ≤ ‖z-y‖} y]

theorem radial_raw_gain_step {J n : ℕ} (S : Nuclei J)
    (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hmass : mass ψ=1)
    {a E δ : ℝ} (ha : 0<a) (y : Space) (hnuc : ∀ j, 3*a ≤ ‖S.position j-y‖)
    (hE : (E:EReal) ≤ unrestrictedFormBottom S) (hstate : form S ψ ≤ E+δ) :
    ∃ (m k : (Fin n → Fin 2) → ℕ) (u : (p : Fin n → Fin 2) → H1Vector (m p+k p))
      (e : (p : Fin n → Fin 2) → Fin (m p+k p) ≃ Fin n),
      (∀ p, m p+k p=n) ∧ (∑ p, mass (u p))=1 ∧
      (∀ p s, ∀ᵐ x, Antisymmetric ((u p).coreSlice s x)) ∧
      (∀ p s, ∀ᵐ x, SpatiallySupported ((u p).coreSlice s x).normalized {z | 40*a ≤ ‖z-y‖}) ∧
      (∀ p s, ∀ᵐ x, mass ((u p).coreSlice s x) ≠0 → ∀ i, ‖position x i-y‖ ≤ 80*a) ∧
      (∀ W : Configuration n → ℝ, Measurable W → (∃ B : ℝ, ∀ x, |W x| ≤ B) →
        (∀ q x, W (permute q x)=W x) →
        (∑ p, potentialForm (fun x => W (reindexConfiguration (e p) x)) (u p))=potentialForm W ψ) ∧
      (∑ p, (m p:ℝ)^2*mass (u p)) ≤ localCountSecondMoment ψ (Metric.closedBall y (80*a)) ∧
      (∀ A : Set Space, MeasurableSet A →
        (∑ p, sliceExpectation (u p) (fun _ x => (localCount A x)^2)) ≤ localCountSecondMoment ψ A) ∧
      a/(16*ballTrialCoefficient)*(∑ p, sliceExpectation (u p) (fun s x =>
        (max (coreConditionalObservable (u p)
          (rawSignedField (attraction S y) {z | 40*a ≤ ‖z-y‖} y) s x) 0)^2)) ≤
      δ+3*(radialCutCoefficient/(40*a))^2*expectedPopulation ψ (Metric.closedBall y (80*a))+
        4*ballTrialCoefficient*(screenBaseMass a)^2/a-∑ p, conditionalOutCost S (u p) := by
  have hr : 0<40*a := by positivity
  let χ := radialCut y (40*a)
  have hc : ∀ z ∉ {z | 40*a ≤ ‖z-y‖}, χ 1 z=0 := by
    intro z hz
    exact radialCut_core_zero y hr z (lt_of_not_ge hz).le
  have ho : ∀ z ∉ Metric.closedBall y (80*a), χ 0 z=0 := by
    intro z hz
    apply radialCut_out_zero y hr
    have h : 80*a < ‖z-y‖ := by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hz
    linarith
  have H (p : Fin n → Fin 2) := binary_cut_recorded_outcome S ψ hψ χ (radialCut_smooth y (40*a))
    (radialCut_partition y (40*a)) (radialCutCoefficient/(40*a))
    (div_nonneg radialCutCoefficient_pos.le hr.le) (radialCut_derivative_bound y hr) p _ _ hc ho
  choose m k u e hn hcount hm hf hobs hanti hs hout using H
  have hsum : (∑ p, mass (u p))=1 := by
    simp_rw [hm]
    rw [mass_labelCut,hmass]
  have hsupport (p) (s : Spins (m p)) : ∀ᵐ x,
      SpatiallySupported ((u p).coreSlice s x).normalized {z | 40*a ≤ ‖z-y‖} := by
    filter_upwards [hs p s] with x hx
    exact hx.normalized
  have houter (p) (s : Spins (m p)) : ∀ᵐ x,
      mass ((u p).coreSlice s x) ≠0 → ∀ i, ‖position x i-y‖ ≤ 80*a := by
    filter_upwards [hout p s] with x hx
    intro hm i
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hx hm i
  have hconserve (W : Configuration n → ℝ) (hW : Measurable W)
      (hB : ∃ B : ℝ, ∀ x, |W x| ≤ B) (hSym : ∀ q x, W (permute q x)=W x) :
      (∑ p, potentialForm (fun x => W (reindexConfiguration (e p) x)) (u p))=potentialForm W ψ := by
    simp_rw [hobs _ W hSym]
    obtain ⟨B,hB⟩ := hB
    exact potentialForm_labelCut ψ χ _ _ _ _ _ W hW hB
  have hmsq : (∑ p, (m p:ℝ)^2*mass (u p)) ≤ localCountSecondMoment ψ (Metric.closedBall y (80*a)) := by
    simp_rw [←hcount,hm]
    exact labelCut_outCount_secondMoment_le ψ χ _ _ _ _ _ _ measurableSet_closedBall ho
  have hcsq (A : Set Space) (hA : MeasurableSet A) :
      (∑ p, sliceExpectation (u p) (fun _ x => (localCount A x)^2)) ≤ localCountSecondMoment ψ A := by
    have hcons := hconserve (fun x => (localCount A x)^2) ((localCount_measurable hA).pow_const 2)
      ⟨(n:ℝ)^2,fun x => by rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (localCount_nonneg _ _) (localCount_le _ _) 2⟩
      (fun q x => by rw [localCount_permute])
    simp only [localCount_reindex] at hcons
    calc
      _ ≤ ∑ p, localCountSecondMoment (u p) A := Finset.sum_le_sum (fun p _ => sliceExpectation_localCount_sq_le (u p) hA)
      _ = _ := hcons
  have hclosed : IsClosed {z : Space | 40*a ≤ ‖z-y‖} := isClosed_le continuous_const (by fun_prop)
  have hg (p : Fin n → Fin 2) :
      a/(16*ballTrialCoefficient)*sliceExpectation (u p) (fun s x =>
        (max (coreScreenedField S ((u p).coreSlice s x).normalized y) 0)^2) ≤
      form S (u p)-conditionalOutCost S (u p)-E*mass (u p)+
        (4*ballTrialCoefficient*(screenBaseMass a)^2/a)*mass (u p) := by
    have HG := conditional_positive_field_gain S (u p) (hanti p) ha y _ hclosed
      (hsupport p) (fun z hz => by change 40*a ≤ ‖z-y‖ at hz; linarith) hnuc hE
    rw [form_eq_conditionalOutCost S (u p)]
    linarith
  have HI : (∑ p, form S (u p)) ≤ E+δ+
      3*(radialCutCoefficient/(40*a))^2*expectedPopulation ψ (Metric.closedBall y (80*a)) := by
    simp_rw [hf]
    have HI := form_radial_labelCut S ψ y hr
    dsimp [χ]
    have he : 2*(40*a)=80*a := by ring
    rw [he] at HI
    exact HI.trans (add_le_add hstate le_rfl)
  have HH := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => hg p)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,hsum,mul_one] at HH
  have hp (p) : sliceExpectation (u p) (fun s x =>
      (max (coreConditionalObservable (u p) (rawSignedField (attraction S y) {z | 40*a ≤ ‖z-y‖} y) s x) 0)^2) ≤
      sliceExpectation (u p) (fun s x => (max (coreScreenedField S ((u p).coreSlice s x).normalized y) 0)^2) := by
    apply Finset.sum_le_sum
    intro s hs'
    apply integral_mono_of_nonneg
    · exact Eventually.of_forall (fun x => mul_nonneg (mass_nonneg _) (sq_nonneg _))
    · exact coreField_positive_square_weight_integrable S (u p) s y
    · filter_upwards [hsupport p s] with x hx
      exact raw_posterior_positive_le_core S (u p) ha y s x hx
  have hco : 0 ≤ a/(16*ballTrialCoefficient) := div_nonneg ha.le (mul_nonneg (by norm_num) ballTrialCoefficient_pos.le)
  have HP := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => hp p)) hco
  refine ⟨m,k,u,e,hn,hsum,hanti,hsupport,houter,hconserve,hmsq,hcsq,?_⟩
  linarith

end Coulomb

end

end OAI
