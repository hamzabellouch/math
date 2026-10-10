import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.RecordedEnsemble
import OAI.Analysis.CoulombRadii.Packets.AtomicMesh

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma RecordedEnsemble.rawSquare_nonneg {n J : ℕ} (T : RecordedEnsemble n) (S : Nuclei J)
    (y : Space) (a : ℝ) : 0 ≤ T.rawSquare S y a := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => integral_nonneg
    (fun _ => mul_nonneg (mass_nonneg _) (sq_nonneg _))))

lemma RecordedEnsemble.rawSquare_le {n J : ℕ} (T : RecordedEnsemble n) (S : Nuclei J)
    (y : Space) {a : ℝ} (ha : 0<a) :
    T.rawSquare S y a ≤ (attraction S y)^2*T.totalMass := by
  rw [RecordedEnsemble.totalMass,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  rw [←sliceExpectation_number]
  unfold sliceExpectation
  apply Finset.sum_le_sum
  intro s hs
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall (fun _ => mul_nonneg (mass_nonneg _) (sq_nonneg _))
  · exact (mass_coreSlice_integrable (T.vector p) s).mul_const _
  · filter_upwards [] with x
    rw [coreConditionalObservable_raw_positive_weight (T.vector p) (attraction S y)
      (A := {z | 40*a ≤ ‖z-y‖})
      (isClosed_le continuous_const (by fun_prop)).measurableSet y
      (show 0<40*a by positivity) (fun _ h => h)]
    apply mul_le_mul_of_nonneg_left _ (mass_nonneg _)
    apply pow_le_pow_left₀ (le_max_right _ _) _ 2
    apply max_le _ (attraction_nonneg S y)
    linarith [restrictedCorePotential_nonneg (T.vector p |>.coreSlice s x |>.normalized) {z | 40*a ≤ ‖z-y‖} y,
      restrictedOutPotential_nonneg x {z | 40*a ≤ ‖z-y‖} y]

lemma attraction_atomic {J : ℕ} (S : Nuclei J) (hatom : ∀ i, S.position i=0) (y : Space) :
    attraction S y=totalCharge S/‖y‖ := by
  simp only [attraction,hatom,sub_zero,coulombKernel,div_eq_mul_inv,totalCharge,Finset.sum_mul]

lemma RecordedEnsemble.rawSquare_atomic_cap {n J : ℕ} (T : RecordedEnsemble n) (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (hm : T.totalMass=1) {y : Space} (hy : y≠0) :
    T.rawSquare S y (atomicCellScale y) ≤ (totalCharge S/(100000*atomicCellScale y))^2 := by
  simpa only [attraction_atomic S hatom,atomicCellScale_norm,hm,mul_one] using
    T.rawSquare_le S y (atomicCellScale_pos hy)

lemma localCount_mono {n : ℕ} {A B : Set Space} (h : A ⊆ B) (x : Configuration n) :
    localCount A x ≤ localCount B x := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases hx : position x i∈A
  · simp [hx,h hx]
  · simp only [indicator_of_notMem hx]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma localCountSecondMoment_mono {n : ℕ} (ψ : H1Vector n) {A B : Set Space}
    (hB : MeasurableSet B) (h : A ⊆ B) :
    localCountSecondMoment ψ A ≤ localCountSecondMoment ψ B := by
  apply Finset.sum_le_sum
  intro s hs
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  · exact localCount_weight_integrable ψ hB s 2
  · exact Eventually.of_forall (fun x => mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (localCount_nonneg A x) (localCount_mono h x) 2) (sq_nonneg _))

end Coulomb
end

end
end

end OAI
