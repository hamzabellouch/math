import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ObservationMatching

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def arrayStatistic {n : ℕ} (χ : Space → ℝ) (x : Configuration n) : ℝ :=
  ∑ i, χ (position x i)

lemma arrayStatistic_measurable {n : ℕ} {χ : Space → ℝ} (hχ : Measurable χ) :
    Measurable (@arrayStatistic n χ) := by
  unfold arrayStatistic
  exact Finset.measurable_fun_sum _ (fun i _ => hχ.comp (continuous_position i).measurable)

lemma arrayStatistic_join {m k : ℕ} (χ : Space → ℝ) (x : Configuration m) (z : Configuration k) :
    arrayStatistic χ (joinConfiguration m k (x,z))=arrayStatistic χ x+arrayStatistic χ z := by
  simp only [arrayStatistic,Fin.sum_univ_add,position_join_left,position_join_right]

lemma arrayStatistic_reindex {m n : ℕ} (χ : Space → ℝ) (e : Fin m ≃ Fin n) (x : Configuration m) :
    arrayStatistic χ (reindexConfiguration e x)=arrayStatistic χ x := by
  change (∑ i : Fin n, χ (position x (e.symm i)))=_
  exact Equiv.sum_comp e.symm (fun i : Fin m => χ (position x i))

lemma arrayStatistic_eq_zero_of_allPositions {n : ℕ} {χ : Space → ℝ} {A : Set Space}
    (hχ : ∀ z∈A, χ z=0) {x : Configuration n} (hx : x∈allPositions A) :
    arrayStatistic χ x=0 := Finset.sum_eq_zero (fun i _ => hχ _ (hx i))

lemma potentialForm_statistic_join_of_support {m k : ℕ} {u : H1Vector k}
    {χ : Space → ℝ} {A : Set Space} (hχ : ∀ z∈A, χ z=0)
    (hu : SpatiallySupported u A) (φ : ℝ → ℝ) (x : Configuration m) :
    potentialForm (fun z => φ (arrayStatistic χ (joinConfiguration m k (x,z)))) u=
      φ (arrayStatistic χ x)*mass u := by
  rw [←potentialForm_const (φ (arrayStatistic χ x)) u]
  apply Finset.sum_congr rfl
  intro s hs
  apply integral_congr_ae
  filter_upwards [hu s] with z hz
  by_cases h : z∈allPositions A
  · rw [arrayStatistic_join,arrayStatistic_eq_zero_of_allPositions hχ h,add_zero]
  · rw [hz h,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,mul_zero]

lemma sliceExpectation_statistic_eq {m k : ℕ} (u : H1Vector (m+k))
    {χ : Space → ℝ} (hχm : Measurable χ) {A : Set Space} (hχ : ∀ z∈A, χ z=0)
    (hu : PartlySupported u (coreIndexSet m k) A) (φ : ℝ → ℝ)
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ q, |φ q|≤B) :
    sliceExpectation u (fun _ x => φ (arrayStatistic χ x))=
      potentialForm (fun x => φ (arrayStatistic χ x)) u := by
  have HH := sliceExpectation_coreConditionalObservable u (fun x => φ (arrayStatistic χ x))
    (hφ.comp (arrayStatistic_measurable hχm)) (fun x => hB _)
  rw [←HH]
  apply Finset.sum_congr rfl
  intro s hs
  apply integral_congr_ae
  filter_upwards [hu.coreSlice s] with x hx
  by_cases hm : mass (u.coreSlice s x)=0
  · simp only [hm,zero_mul]
  · unfold coreConditionalObservable
    rw [potentialForm_statistic_join_of_support hχ hx.normalized φ x,
      mass_normalized _ (lt_of_le_of_ne (mass_nonneg _) (Ne.symm hm)),mul_one]

lemma RecordedEnsemble.Conserves.statistic {n : ℕ} {T : RecordedEnsemble n}
    {ψ : H1Vector n} (hT : T.Conserves ψ) {χ : Space → ℝ} (hχm : Measurable χ)
    {A : Set Space} (hχ : ∀ z∈A, χ z=0) (hcs : T.CoreSupported A)
    (φ : ℝ → ℝ) (hφ : Measurable φ) {B : ℝ} (hB : ∀ q, |φ q|≤B) :
    (∑ p, sliceExpectation (T.vector p) (fun _ x => φ (arrayStatistic χ x)))=
      potentialForm (fun x => φ (arrayStatistic χ x)) ψ := by
  have H := hT (fun x => φ (arrayStatistic χ x)) (hφ.comp (arrayStatistic_measurable hχm)) ⟨B,fun x => hB _⟩
  simp only [Function.comp_def,arrayStatistic_reindex] at H
  rw [←H]
  exact Finset.sum_congr rfl (fun p _ => sliceExpectation_statistic_eq (T.vector p) hχm hχ (hcs p) φ hφ hB)

theorem RecordedEnsemble.Conserves.statistic_event_ae {n : ℕ} {T : RecordedEnsemble n}
    {ψ : H1Vector n} (hT : T.Conserves ψ) {χ : Space → ℝ} (hχm : Measurable χ)
    {A : Set Space} (hχ : ∀ z∈A, χ z=0) (hcs : T.CoreSupported A)
    {B : Set ℝ} (hB : MeasurableSet B)
    (hzero : potentialForm (fun x => Bᶜ.indicator (fun _ => (1:ℝ)) (arrayStatistic χ x)) ψ=0) :
    ∀ p s, ∀ᵐ x, mass ((T.vector p).coreSlice s x)≠0 → arrayStatistic χ x∈B := by
  let φ : ℝ → ℝ := Bᶜ.indicator (fun _ => 1)
  have hφ : Measurable φ := measurable_const.indicator hB.compl
  have hφ0 (q : ℝ) : 0≤φ q := indicator_nonneg (fun _ _ => zero_le_one) q
  have hφ1 (q : ℝ) : |φ q|≤1 := by
    dsimp [φ]
    by_cases h : q∈Bᶜ <;> simp [h]
  have HI (p : T.index) (s : Spins (T.out p)) :
      Integrable (fun x => mass ((T.vector p).coreSlice s x)*φ (arrayStatistic χ x)) := by
    have H := (mass_coreSlice_integrable (T.vector p) s).bdd_mul
      (hφ.comp (arrayStatistic_measurable hχm)).aestronglyMeasurable
      (Eventually.of_forall (fun x => (show ‖φ (arrayStatistic χ x)‖≤1 by simpa only [Real.norm_eq_abs] using hφ1 _)))
    exact H.congr (Eventually.of_forall (fun x => mul_comm _ _))
  have H0 (p : T.index) (s : Spins (T.out p)) (x : Configuration (T.out p)) :
      0 ≤ mass ((T.vector p).coreSlice s x)*φ (arrayStatistic χ x) := mul_nonneg (mass_nonneg _) (hφ0 _)
  have H := hT.statistic hχm hχ hcs φ hφ hφ1
  rw [show potentialForm (fun x => φ (arrayStatistic χ x)) ψ=0 from hzero] at H
  have Hs := (Finset.sum_eq_zero_iff_of_nonneg (fun p (_ : p∈Finset.univ) =>
    Finset.sum_nonneg (fun s _ => integral_nonneg (H0 p s)))).mp H
  intro p s
  have Hss := (Finset.sum_eq_zero_iff_of_nonneg (fun s (_ : s∈Finset.univ) =>
    integral_nonneg (H0 p s))).mp (Hs p (Finset.mem_univ _)) s (Finset.mem_univ _)
  have Hae := (integral_eq_zero_iff_of_nonneg (H0 p s) (HI p s)).mp Hss
  filter_upwards [Hae] with x hx
  intro hm
  have hz : φ (arrayStatistic χ x)=0 := (mul_eq_zero.mp hx).resolve_left hm
  by_contra hb
  have he : φ (arrayStatistic χ x)=1 := indicator_of_mem hb _
  linarith

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

theorem arrayEvent_fresh_statistic_ae {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, ℓ h≠0)
    {E : Set ((H × (Fin n × Fin 3)) → ℝ)} (hE : MeasurableSet E)
    (ψ : Wavefunction n) (u : Coulomb.H1Vector n)
    (hbayes : ∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ E))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ E x*F (flattenConfiguration n x)))
    (T : Coulomb.RecordedEnsemble n) (hT : T.Conserves u)
    {χ : Position → ℝ} (hχm : Measurable χ) {A : Set Position}
    (hχ : ∀ z∈A, χ z=0) (hcs : T.CoreSupported A)
    {B : Set ℝ} (hB : MeasurableSet B)
    (hmatch : ∀ (x : Configuration n) (z : (H × (Fin n × Fin 3)) → ℝ),
      (∀ ia, |z ia|<1) → (fun ia => x ia.2.1 ia.2.2+ℓ ia.1*z ia)∈E →
      Coulomb.arrayStatistic χ (flattenConfiguration n x)∈B) :
    ∀ p s, ∀ᵐ x, Coulomb.mass ((T.vector p).coreSlice s x)≠0 →
      Coulomb.arrayStatistic χ x∈B := by
  apply hT.statistic_event_ae hχm hχ hcs hB
  rw [hbayes]
  have hz : stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ E x*
      Bᶜ.indicator (fun _ => (1:ℝ)) (Coulomb.arrayStatistic χ (flattenConfiguration n x)))=0 := by
    unfold stateWeightedIntegral
    apply Finset.sum_eq_zero
    intro s hs
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    by_cases hp : arrayEventLikelihood ℓ E x=0
    · simp [hp]
    · have hpos := lt_of_le_of_ne (arrayEventLikelihood_nonneg ℓ hE x) (Ne.symm hp)
      obtain ⟨z,hz,he⟩ := arrayEventLikelihood_pos_matching ℓ hℓ E x hpos
      have hb := hmatch x z hz he
      simp only [Set.indicator_of_notMem (show Coulomb.arrayStatistic χ (flattenConfiguration n x)∉Bᶜ from not_not.mpr hb),mul_zero,zero_mul]
      rfl
  rw [hz,mul_zero]

end NeutralAtom
namespace Coulomb

theorem arrayStatistic_local_matching {n : ℕ} (χ : Space → ℝ) (x z : Configuration n)
    (y : Space) {r d L : ℝ} (hd : 0≤d) (hL : 0≤L)
    (hs : ∀ v, χ v≠0 → ‖v-y‖≤r)
    (hLip : ∀ v w, |χ v-χ w|≤L*‖v-w‖)
    (hmatch : ∀ i, ‖position z i-position x i‖≤d) :
    |arrayStatistic χ z-arrayStatistic χ x|≤
      (L*d)*localCount (Metric.closedBall y (r+d)) x := by
  have Hone (i : Fin n) : |χ (position z i)-χ (position x i)|≤
      (L*d)*(Metric.closedBall y (r+d)).indicator (fun _ => (1:ℝ)) (position x i) := by
    by_cases hx : position x i∈Metric.closedBall y (r+d)
    · rw [indicator_of_mem hx,mul_one]
      exact (hLip _ _).trans (mul_le_mul_of_nonneg_left (hmatch i) hL)
    · rw [indicator_of_notMem hx,mul_zero]
      have hxx : χ (position x i)=0 := by
        by_contra h
        apply hx
        rw [Metric.mem_closedBall,dist_eq_norm]
        exact (hs _ h).trans (by linarith)
      have hzz : χ (position z i)=0 := by
        by_contra h
        apply hx
        rw [Metric.mem_closedBall,dist_eq_norm]
        have ht := norm_sub_le_norm_sub_add_norm_sub (position x i) (position z i) y
        have hh := hmatch i
        rw [norm_sub_rev (position z i) (position x i)] at hh
        linarith [hs _ h]
      simp [hxx,hzz]
  calc
    _ = |∑ i, (χ (position z i)-χ (position x i))| := by rw [Finset.sum_sub_distrib]; rfl
    _ ≤ ∑ i, |χ (position z i)-χ (position x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (L*d)*(Metric.closedBall y (r+d)).indicator (fun _ => (1:ℝ)) (position x i) :=
      Finset.sum_le_sum (fun i _ => Hone i)
    _ = _ := by rw [←Finset.mul_sum]; rfl

end Coulomb

end

end OAI
