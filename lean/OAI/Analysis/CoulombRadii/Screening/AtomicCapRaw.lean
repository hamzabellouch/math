import Mathlib
import OAI.Analysis.CoulombRadii.Screening.OutCap
import OAI.Analysis.CoulombRadii.Packets.AtomicMesh

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma farSquare_to_atomic_raw {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {z v : Space} (hz : z≠0) (hv : ‖v-z‖ ≤ 2*atomicCellScale z) :
    sliceExpectation u (fun s x =>
      (max (recordedFarField S (u.coreSlice s x).normalized x {w | 4*atomicCellScale z ≤ ‖w-z‖} v) 0)^2) ≤
    sliceExpectation u (fun s x =>
      (max (coreConditionalObservable u
        (rawSignedField (attraction S v) {w | 40*atomicCellScale v ≤ ‖w-v‖} v) s x) 0)^2) := by
  have hv0 : v≠0 := atomicCellScale_near_nonzero hz (by nlinarith [atomicCellScale_nonneg z])
  have hvpos := atomicCellScale_pos hv0
  have hp : 0<40*atomicCellScale v := by positivity
  have hA : MeasurableSet {w : Space | 40*atomicCellScale v ≤ ‖w-v‖} :=
    (isClosed_le continuous_const (by fun_prop)).measurableSet
  have hB : MeasurableSet {w : Space | 4*atomicCellScale z ≤ ‖w-z‖} :=
    (isClosed_le continuous_const (by fun_prop)).measurableSet
  have hb := rawSignedField_abs_le (n:=m+k) (attraction S v) _ v hp (fun _ h => h)
  have hB0 : 0 ≤ |attraction S v|+((m+k:ℕ):ℝ)/(40*atomicCellScale v) := by positivity
  apply Finset.sum_le_sum
  intro s hs
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall (fun _ => mul_nonneg (mass_nonneg _) (sq_nonneg _))
  · exact coreConditionalObservable_positive_weight_integrable u _
      (rawSignedField_measurable _ hA v) hB0 hb s 2
  · filter_upwards [] with x
    by_cases hm : mass (u.coreSlice s x)=0
    · simp only [hm,zero_mul,le_refl]
    · have hm' := lt_of_le_of_ne (mass_nonneg (u.coreSlice s x)) (Ne.symm hm)
      rw [coreConditionalObservable_rawSignedField u _ hA v hp (fun _ h => h) s x hm']
      apply mul_le_mul_of_nonneg_left _ (mass_nonneg _)
      apply pow_le_pow_left₀ (le_max_right _ _) _ 2
      apply max_le_max _ le_rfl
      exact recordedFarField_anti S (u.coreSlice s x).normalized x hA hB (atomic_raw_exclusion_subset hv) v

lemma sliceFarSquare_ballCloud_integrable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) {A : Set Space} (hA : MeasurableSet A)
    {a : ℝ} (ha : 0<a) (y : Space) (hnuc : ∀ j, 2*a ≤ ‖S.position j-y‖) :
    Integrable (fun v => (sliceExpectation u (fun s x =>
      (max (recordedFarField S (u.coreSlice s x).normalized x A v) 0)^2))*ballCloud y a 1 v) := by
  unfold sliceExpectation
  simp only [Finset.sum_mul,←integral_mul_const]
  exact integrable_finsetSum _ (fun s _ =>
    (farSquare_mass_ballCloud_integrable S u s hA ha y hnuc).integral_prod_right)

theorem atomic_cap_sq_le_of_raw_bound {P : Type*} [Fintype P] {J : ℕ}
    (S : Nuclei J) (m k : P → ℕ) (u : (p : P) → H1Vector (m p+k p))
    {z : Space} (hz : z≠0) (hnuc : ∀ j, 4*atomicCellScale z ≤ ‖S.position j-z‖)
    {H : ℝ} (hraw : ∀ v : Space, ‖v-z‖ ≤ 2*atomicCellScale z →
      (∑ p, sliceExpectation (u p) (fun s x =>
        (max (coreConditionalObservable (u p)
          (rawSignedField (attraction S v) {w | 40*atomicCellScale v ≤ ‖w-v‖} v) s x) 0)^2)) ≤ H) :
    (∑ p, sliceExpectation (u p) (fun s x =>
      (localFarCap S ((u p).coreSlice s x).normalized x z (atomicCellScale z))^2)) ≤ 8*H := by
  have ha := atomicCellScale_pos hz
  let A := {w : Space | 4*atomicCellScale z ≤ ‖w-z‖}
  have hA : MeasurableSet A := (isClosed_le continuous_const (by fun_prop)).measurableSet
  let F := fun p v => sliceExpectation (u p) (fun s x =>
    (max (recordedFarField S ((u p).coreSlice s x).normalized x A v) 0)^2)
  have hi (p) : Integrable (fun v => F p v*ballCloud z (2*atomicCellScale z) 1 v) :=
    sliceFarSquare_ballCloud_integrable S (u p) hA (by positivity) z (fun j => by nlinarith [hnuc j])
  have hb : Integrable (fun v => H*ballCloud z (2*atomicCellScale z) 1 v) := (ballCloud_integrable _ _ _).const_mul H
  have hsum : (∫ v, ∑ p, F p v*ballCloud z (2*atomicCellScale z) 1 v) ≤ H := by
    calc
      _ ≤ ∫ v, H*ballCloud z (2*atomicCellScale z) 1 v := by
        apply integral_mono (integrable_finsetSum _ (fun p _ => hi p)) hb
        intro v
        change (∑ p, F p v*ballCloud z (2*atomicCellScale z) 1 v) ≤ H*ballCloud z (2*atomicCellScale z) 1 v
        rw [←Finset.sum_mul]
        by_cases hv : v-z ∈ Metric.ball (0:Space) (2*atomicCellScale z)
        · have hdist : ‖v-z‖ ≤ 2*atomicCellScale z := by
            exact (by simpa only [Metric.mem_ball,dist_zero_right] using hv : ‖v-z‖ < 2*atomicCellScale z).le
          apply mul_le_mul_of_nonneg_right _ (uniformBall_nonneg (by positivity) zero_le_one (v-z))
          exact (Finset.sum_le_sum (fun p _ => farSquare_to_atomic_raw S (u p) hz hdist)).trans (hraw v hdist)
        · simp only [ballCloud,uniformBall,indicator_of_notMem hv,mul_zero,le_refl]
      _ = H := by rw [integral_const_mul,ballCloud_mass (by positivity) 1 z,mul_one]
  calc
    _ = ∑ p, 8*(∫ v, F p v*ballCloud z (2*atomicCellScale z) 1 v) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact sliceExpectation_localFarCap_sq S (u p) ha z hnuc
    _ = 8*(∫ v, ∑ p, F p v*ballCloud z (2*atomicCellScale z) 1 v) := by
      rw [←Finset.mul_sum,integral_finsetSum _ (fun p _ => hi p)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)

end Coulomb
end

end
end

end OAI
