import Mathlib
import OAI.Analysis.CoulombIonization.Localization.BarrierEventSymmetryBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set

namespace CoulombAtom
open CoulombObservation

@[instance_reducible] def tailInvariantArraySpace (N K j : ℕ) :
    MeasurableSpace (Fin K × (Fin N × Fin 3) → ℝ) where
  MeasurableSet' A := ∀ (u v : Fin K × (Fin N × Fin 3) → ℝ), (∀ k : Fin K, j ≤ k.val → ∀ (i : Fin N) (a : Fin 3), u (k,i,a) = v (k,i,a)) →
    (u ∈ A ↔ v ∈ A)
  measurableSet_empty := fun _ _ _ => Iff.rfl
  measurableSet_compl := fun _ h u v huv => not_congr (h u v huv)
  measurableSet_iUnion := by
    intro f h u v huv
    simp only [mem_iUnion]
    exact exists_congr (fun n => h n u v huv)

lemma arrayObservationInformation_le_tailInvariant (N K j : ℕ) :
    arrayObservationInformation N K j ≤ tailInvariantArraySpace N K j := by
  apply iSup_le
  intro k
  split_ifs with hk
  · intro A hA
    obtain ⟨B,_,rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
    intro u v huv
    have he : arrayUnorderedConfiguration k u = arrayUnorderedConfiguration k v := by
      apply congrArg unorderedConfiguration
      funext i
      ext a
      exact huv k hk i a
    exact congrArg (· ∈ B) he |>.to_iff
  · exact bot_le

lemma observation_event_tail_representation {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation ell j] A) :
    ∃ B : Set (Fin K × (Fin N × Fin 3) → ℝ),
      MeasurableSet[arrayObservationInformation N K j] B ∧ physicalObservationEvent ell B = A := by
  rw [observationInformation_eq_arrayComap] at hA
  exact MeasurableSpace.measurableSet_comap.mp hA

def tailObservationCoefficient {K : ℕ} (ell : Fin K → ℝ) (j : ℕ) (k : Fin K) : ℝ :=
  if j ≤ k.val then (ell k)⁻¹ else 0

lemma tail_physicalObservationEvent_eq {N K : ℕ}
    (ell : Fin K → ℝ) (hell : ∀ k, 0 < ell k) (j : ℕ)
    {B : Set (Fin K × (Fin N × Fin 3) → ℝ)}
    (hB : MeasurableSet[arrayObservationInformation N K j] B) :
    quantumObservationEvent (tailObservationCoefficient ell j) (scaleObservationArray ell ⁻¹' B) =
      physicalObservationEvent ell B := by
  ext z
  apply arrayObservationInformation_le_tailInvariant N K j B hB
  intro k hk i a
  simp only [scaleObservationArray_apply,Pi.add_apply,observationPlacement_apply,
    flattenConfiguration_apply,physicalObservationArray,tailObservationCoefficient,ite_eq_left hk]
  rw [mul_add,←mul_assoc,mul_inv_cancel₀ (hell k).ne',one_mul]

lemma tail_quantumEventProbability_eq_physical {N K : ℕ}
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2 = 1)
    (ell : Fin K → ℝ) (hell : ∀ k, 0 < ell k) (j : ℕ)
    {B : Set (Fin K × (Fin N × Fin 3) → ℝ)}
    (hB : MeasurableSet[arrayObservationInformation N K j] B) :
    quantumEventProbability F (tailObservationCoefficient ell j) (scaleObservationArray ell ⁻¹' B) =
      physicalObservationProbability F ell B := by
  have hm := (arrayObservationInformation_le N K j B hB).preimage (scaleObservationArray ell).measurable
  have he := quantumEventProbability_ofReal F hn (tailObservationCoefficient ell j) hm
  rw [tail_physicalObservationEvent_eq ell hell j hB] at he
  exact (ENNReal.toReal_ofReal (integral_nonneg (quantumEventLikelihood_nonneg _ hm))).symm.trans
    (congrArg ENNReal.toReal he)
end CoulombAtom

open MeasureTheory Set Finset
open scoped BigOperators

namespace CoulombObservation
lemma geometric_tail_sum_le_two {q : ℝ} (hq : 0 ≤ q) (hq2 : q ≤ 1/2) (j K : ℕ) :
    (∑ k : Fin K, if j ≤ k.val then q^k.val else 0) ≤ 2*q^j := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if j ≤ k then q^k else 0) K,
    ←Finset.sum_filter]
  have he : (range K).filter (fun k => j ≤ k) = Finset.Ico j K := by
    ext k
    simp only [mem_filter,Finset.mem_range,Finset.mem_Ico]
    tauto
  rw [he]
  have hh := geom_sum_Ico_le_of_lt_one (m := j) (n := K) hq (by linarith : q < 1)
  apply hh.trans
  apply (div_le_iff₀ (by linarith : 0 < 1-q)).mpr
  nlinarith [pow_nonneg hq j,mul_le_mul_of_nonneg_right hq2 (pow_nonneg hq j)]
end CoulombObservation
namespace CoulombAtom
open CoulombObservation

lemma tail_dyadicObservation_inv_sq_sum {r : ℝ} (hr : 0 < r) (j K : ℕ) :
    (∑ k : Fin K, (tailObservationCoefficient (fun k => dyadicObservationWidth r k) j k)^2) ≤
      2*((2:ℝ)^j*r)^(-2.02:ℝ) := by
  have he (k : Fin K) : (tailObservationCoefficient (fun k => dyadicObservationWidth r k) j k)^2 =
      r^(-2.02:ℝ)*(if j ≤ k.val then ((2:ℝ)^(-2.02:ℝ))^k.val else 0) := by
    unfold tailObservationCoefficient
    split_ifs
    · exact dyadicObservationWidth_inv_sq hr k
    · simp
  simp_rw [he]
  rw [←mul_sum]
  have hh := mul_le_mul_of_nonneg_left
    (geometric_tail_sum_le_two dyadicObservationRatio_nonneg dyadicObservationRatio_le_half j K)
    (Real.rpow_nonneg hr.le (-2.02))
  apply hh.trans_eq
  rw [Real.mul_rpow (by positivity) hr.le,←Real.rpow_pow_comm (by norm_num)]
  ring

lemma tail_observationTiltEnergyCost_dyadic {r p : ℝ} (hr : 0 < r) (hp : 0 < p)
    (hp1 : p ≤ 1) (j K : ℕ) :
    (observationFisherConstant/2)*
      (∑ k : Fin K, (tailObservationCoefficient (fun k => dyadicObservationWidth r k) j k)^2)*
      (Real.log (Real.exp 1/p))^5 ≤
      observationFisherConstant*((2:ℝ)^j*r)^(-2.02:ℝ)*(Real.log (Real.exp 1/p))^5 := by
  have hlog : 0 ≤ (Real.log (Real.exp 1/p))^5 := by
    apply pow_nonneg
    rw [eventLog_eq hp]
    linarith [Real.log_nonpos hp.le hp1]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (tail_dyadicObservation_inv_sq_sum hr j K)
      (show 0 ≤ observationFisherConstant/2 by linarith [observationFisherConstant_pos])) hlog
  exact hh.trans_eq (by ring)
end CoulombAtom

end

end OAI
