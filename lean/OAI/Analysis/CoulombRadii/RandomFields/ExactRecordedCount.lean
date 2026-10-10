import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.RecordedEnsemble
import OAI.Analysis.CoulombRadii.ThomasFermi.BinaryEnsemble

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma localCount_eq_zero_of_allPositions {n : ℕ} {A B : Set Space} (hAB : Disjoint A B)
    {x : Configuration n} (hx : x∈allPositions A) : localCount B x=0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply indicator_of_notMem
  exact fun h => Set.disjoint_left.mp hAB (hx i) h

lemma potentialForm_count_join_of_support {m k : ℕ} {u : H1Vector k}
    {A B : Set Space} (hAB : Disjoint A B) (hu : SpatiallySupported u A) (x : Configuration m) :
    potentialForm (fun z => (localCount B (joinConfiguration m k (x,z)))^2) u=
      (localCount B x)^2*mass u := by
  rw [←potentialForm_const ((localCount B x)^2) u]
  apply Finset.sum_congr rfl
  intro s hs
  apply integral_congr_ae
  filter_upwards [hu s] with z hz
  by_cases h : z∈allPositions A
  · rw [localCount_join,localCount_eq_zero_of_allPositions hAB h,add_zero]
  · rw [hz h,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,mul_zero]

lemma sliceExpectation_localCount_sq_eq {m k : ℕ} (u : H1Vector (m+k))
    {A B : Set Space} (hB : MeasurableSet B) (hAB : Disjoint A B)
    (hu : PartlySupported u (coreIndexSet m k) A) :
    sliceExpectation u (fun _ x => (localCount B x)^2)=localCountSecondMoment u B := by
  let W := fun x : Configuration (m+k) => (localCount B x)^2
  have hWB : ∀ x, |W x|≤((m+k:ℕ):ℝ)^2 := by
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (localCount_nonneg _ _) (localCount_le _ _) 2
  change sliceExpectation u (fun _ x => (localCount B x)^2)=potentialForm W u
  rw [←sliceExpectation_coreConditionalObservable u W ((localCount_measurable hB).pow_const 2) hWB]
  apply Finset.sum_congr rfl
  intro s hs
  apply integral_congr_ae
  filter_upwards [hu.coreSlice s] with x hx
  by_cases hm : mass (u.coreSlice s x)=0
  · simp only [hm,zero_mul]
  · have hm' := lt_of_le_of_ne (mass_nonneg (u.coreSlice s x)) (Ne.symm hm)
    unfold coreConditionalObservable
    rw [potentialForm_count_join_of_support hAB hx.normalized x,mass_normalized _ hm',mul_one]

lemma RecordedEnsemble.Conserves.recorded_secondMoment_eq {n : ℕ} {T : RecordedEnsemble n}
    {ψ : H1Vector n} (hT : T.Conserves ψ) {A B : Set Space} (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hcs : T.CoreSupported A) :
    (∑ p, sliceExpectation (T.vector p) (fun _ x => (localCount B x)^2))=localCountSecondMoment ψ B := by
  rw [←hT.secondMoment hB]
  exact Finset.sum_congr rfl (fun p _ => sliceExpectation_localCount_sq_eq (T.vector p) hB hAB (hcs p))

end Coulomb
end

end
end

end OAI
