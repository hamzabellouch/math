import OAI.NumberTheory.DukePrimeDegree.Dynamics.PublishedEKL

namespace OAI

/-!
# Exact scaling of the mean root information

The actual normalized leaf information is additive under the canonical
flow. Monotonicity and rational approximation promote its integer-time
scaling law to every nonnegative real time, including infinite means.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
  (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
  (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

include hA

def rootInformationHom : ℝ≥0 →+ ℝ≥0∞ where
  toFun t := rootInformationMean hij μ t
  map_zero' := rootInformationMean_zero_time d hij μ hA
  map_add' s t := rootInformationMean_add d hij μ hA s.property t.property

lemma rootInformationMean_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    rootInformationMean hij μ s ≤ rootInformationMean hij μ t := by
  have he := rootInformationMean_add d hij μ hA hs (sub_nonneg.mpr hst)
  rw [add_sub_cancel] at he
  rw [he]
  exact le_add_right le_rfl

lemma rootInformationMean_rat (m n : ℕ) :
    rootInformationMean hij μ ((m : ℝ) / n) =
      ENNReal.ofReal ((m : ℝ) / n) * rootInformationMean hij μ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [rootInformationMean_zero_time d hij μ hA]
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  let f := rootInformationHom d hij μ hA
  have hdiv : ((m : ℝ≥0) / n) = (n⁻¹ : ℝ≥0) • (m : ℝ≥0) := by
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hm : f (m : ℝ≥0) = (m : ℝ≥0∞) * f 1 := by
    simpa only [nsmul_eq_mul, mul_one] using f.map_nsmul m (1 : ℝ≥0)
  have h := map_inv_natCast_smul f ℝ≥0 ℝ≥0 n (m : ℝ≥0)
  rw [← hdiv, hm, ENNReal.smul_def, smul_eq_mul] at h
  change rootInformationMean hij μ (↑((m : ℝ≥0) / n)) =
    (↑((n : ℝ≥0)⁻¹) : ℝ≥0∞) * ((m : ℝ≥0∞) * rootInformationMean hij μ 1) at h
  rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast,
    ENNReal.coe_inv (by exact_mod_cast hn), ENNReal.coe_natCast] at h
  rw [ENNReal.ofReal_div_of_pos hnpos, ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, div_eq_mul_inv]
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

/-- The mean at time one is the exact coefficient at every positive scale. -/
theorem rootInformationMean_real {t : ℝ} (ht : 0 ≤ t) :
    rootInformationMean hij μ t =
      ENNReal.ofReal t * rootInformationMean hij μ 1 := by
  by_cases ht0 : t = 0
  · subst t
    simp [rootInformationMean_zero_time d hij μ hA]
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let lo (n : ℕ) : ℝ := (⌊t * (n + 1 : ℝ)⌋₊ : ℝ) / (n + 1 : ℝ)
  let hi (n : ℕ) : ℝ := (⌈t * (n + 1 : ℝ)⌉₊ : ℝ) / (n + 1 : ℝ)
  have hn : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hlo : Tendsto lo atTop (𝓝 t) := (tendsto_nat_floor_mul_div_atTop ht).comp hn
  have hhi : Tendsto hi atTop (𝓝 t) := (tendsto_nat_ceil_mul_div_atTop ht).comp hn
  have hlo_le (n : ℕ) : lo n ≤ t := by
    dsimp only [lo]
    rw [div_le_iff₀ (by positivity)]
    exact Nat.floor_le (by positivity)
  have hle_hi (n : ℕ) : t ≤ hi n := by
    dsimp only [hi]
    rw [le_div_iff₀ (by positivity)]
    exact Nat.le_ceil _
  have hlo0 (n : ℕ) : 0 ≤ lo n := by dsimp [lo]; positivity
  have hlot := ENNReal.Tendsto.mul_const (ENNReal.continuous_ofReal.tendsto t |>.comp hlo)
    (b := rootInformationMean hij μ 1) (Or.inl (ENNReal.ofReal_pos.mpr htp).ne')
  have hhit := ENNReal.Tendsto.mul_const (ENNReal.continuous_ofReal.tendsto t |>.comp hhi)
    (b := rootInformationMean hij μ 1) (Or.inl (ENNReal.ofReal_pos.mpr htp).ne')
  apply le_antisymm
  · apply ge_of_tendsto hhit
    apply Eventually.of_forall
    intro n
    have hm := rootInformationMean_mono d hij μ hA ht (hle_hi n)
    have hr := rootInformationMean_rat d hij μ hA ⌈t * (n + 1 : ℝ)⌉₊ (n + 1)
    have hr' : rootInformationMean hij μ (hi n) =
        ENNReal.ofReal (hi n) * rootInformationMean hij μ 1 := by
      simpa only [hi, Nat.cast_add, Nat.cast_one] using hr
    exact hm.trans_eq hr'
  · apply le_of_tendsto hlot
    apply Eventually.of_forall
    intro n
    have hm := rootInformationMean_mono d hij μ hA (hlo0 n) (hlo_le n)
    have hr := rootInformationMean_rat d hij μ hA ⌊t * (n + 1 : ℝ)⌋₊ (n + 1)
    have hr' : rootInformationMean hij μ (lo n) =
        ENNReal.ofReal (lo n) * rootInformationMean hij μ 1 := by
      simpa only [lo, Nat.cast_add, Nat.cast_one] using hr
    exact hr'.symm.trans_le hm

end DukePrimeDegree

end

end OAI
