import OAI.Probability.Localization.History

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma volume_cellSet_ne_zero {n : ℕ} (hn : 0 < n) (Q : Cell n) : volume (cellSet Q) ≠ 0 := by
  rw [volume_cellSet]
  exact ENNReal.ofReal_ne_zero_iff.mpr (pow_pos (cellWidth_pos hn) _)

lemma volume_cellSet_ne_top {n : ℕ} (Q : Cell n) : volume (cellSet Q) ≠ ∞ := by
  rw [volume_cellSet]
  exact ENNReal.ofReal_ne_top

lemma uniformCell_probability {n : ℕ} (hn : 0 < n) (Q : Cell n) : IsProbabilityMeasure (uniformCell Q) :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite (volume_cellSet_ne_zero hn Q) (volume_cellSet_ne_top Q)

lemma uniformCell_self {n : ℕ} (hn : 0 < n) (Q : Cell n) : uniformCell Q (cellSet Q) = 1 :=
  ProbabilityTheory.cond_apply_self (volume_cellSet_ne_zero hn Q) (volume_cellSet_ne_top Q)

lemma uniformCell_ae_mem {n : ℕ} (Q : Cell n) : ∀ᵐ z ∂uniformCell Q,z ∈ cellSet Q :=
  ProbabilityTheory.ae_cond_mem (measurableSet_cellSet Q)

lemma ae_mem_cell_of_ac {n : ℕ} {P : Measure (Coordinate n)} {Q : Cell n}
    (hac : P ≪ uniformCell Q) : ∀ᵐ z ∂P,z ∈ cellSet Q := hac.ae_le (uniformCell_ae_mem Q)

lemma uniformCell_cond {n : ℕ} {Q R : Cell n} (hQR : Descendant Q R) :
    ProbabilityTheory.cond (uniformCell Q) (cellSet R) = uniformCell R := by
  unfold uniformCell
  rw [ProbabilityTheory.cond_cond_eq_cond_inter' (measurableSet_cellSet Q)
    (measurableSet_cellSet R) (volume_cellSet_ne_top Q),Set.inter_eq_right.mpr hQR.2]

lemma uniformCell_eq_cond_prior {n : ℕ} (hn : 0 < n) (Q : Cell n) :
    uniformCell Q = ProbabilityTheory.cond (cubePrior n) (cellSet Q) := by
  unfold cubePrior uniformCell
  rw [ProbabilityTheory.cond_cond_eq_cond_inter' (measurable_initialCube n)
    (measurableSet_cellSet Q) (volume_initialCube_ne_top n),
    Set.inter_eq_right.mpr (cellSet_subset_initialCube hn Q)]

lemma uniformCell_descendant_mass {n : ℕ} (hn : 0 < n) {Q R : Cell n} (hQR : Descendant Q R) :
    uniformCell Q (cellSet R) = ENNReal.ofReal ((1/2:ℝ)^(n*(R.1-Q.1))) := by
  rw [uniformCell_eq_cond_prior hn Q,ProbabilityTheory.cond_apply (measurableSet_cellSet Q),
    Set.inter_eq_right.mpr hQR.2,cubePrior_cellSet hn Q,cubePrior_cellSet hn R]
  rw [← ENNReal.ofReal_inv_of_pos (by positivity : 0 < (1/2:ℝ)^(n*Q.1)),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have he : n*R.1 = n*Q.1+n*(R.1-Q.1) := by
    rw [← Nat.mul_add,Nat.add_sub_of_le hQR.1]
  rw [he,pow_add]
  exact inv_mul_cancel_left₀ (pow_ne_zero _ (by norm_num : (1 / 2 : ℝ) ≠ 0)) _

lemma uniformCell_descendant_pos {n : ℕ} (hn : 0 < n) {Q R : Cell n} (hQR : Descendant Q R) :
    uniformCell Q (cellSet R) ≠ 0 := by
  rw [uniformCell_descendant_mass hn hQR]
  exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)

lemma uniformCell_log_mass {n : ℕ} (hn : 0 < n) {Q R : Cell n} (hQR : Descendant Q R) :
    Real.log ((uniformCell Q (cellSet R)).toReal) = -(n:ℝ)*((R.1-Q.1:ℕ):ℝ)*Real.log 2 := by
  rw [uniformCell_descendant_mass hn hQR,ENNReal.toReal_ofReal (by positivity),Real.log_pow]
  simp only [one_div,Real.log_inv,Nat.cast_mul]
  ring

lemma cond_congr_ae {α : Type*} [MeasurableSpace α] (P : Measure α) {E F : Set α}
    (h : E =ᵐ[P] F) : ProbabilityTheory.cond P E = ProbabilityTheory.cond P F := by
  unfold ProbabilityTheory.cond
  rw [measure_congr h,Measure.restrict_congr_set h]

lemma run_fiber_ae_event {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) (N : ℕ) {z : Coordinate n} (hz : z ∈ cellSet Q) :
    {w | run P Q N w = run P Q N z} =ᵐ[P] (state P Q (run P Q N z)).event := by
  filter_upwards [hroot] with w hw
  exact propext (run_eq_iff_mem hn P Q N hz hw)

lemma terminal_fiber_ae_event {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) {z : Coordinate n} (hz : z ∈ cellSet Q) (ht : Terminates P Q z) :
    {w | terminalLog P Q w = terminalLog P Q z} =ᵐ[P] (state P Q (terminalLog P Q z)).event := by
  have he := terminalLog_fiber_inter_initial hn P Q hz ht
  filter_upwards [hroot] with w hw
  apply propext
  constructor
  · intro hm
    rw [← he]
    exact ⟨hw,hm⟩
  · intro hm
    rw [← he] at hm
    exact hm.2

end FiniteEntropy

end RepeatedLocalization

end OAI
