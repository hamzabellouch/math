import OAI.Probability.SLE.Mass.MassCompensatorMesh

namespace OAI

/-! The last full dyadic cell before a finite or infinite time. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma compensatorMeshTime_eq_div (n i : ℕ) :
    compensatorMeshTime n i = (i:ℝ≥0)/(2:ℝ≥0)^n := by
  simp only [compensatorMeshTime,zpow_neg,zpow_natCast,div_eq_mul_inv]

@[simp] lemma compensatorMeshTime_end (n : ℕ) :
    compensatorMeshTime n (n*2^n) = n := by
  rw [compensatorMeshTime_eq_div]
  push_cast
  exact mul_div_cancel_right₀ _ (by positivity)

def compensatorFiniteIndex (n : ℕ) (t : ℝ≥0) : ℕ :=
  min (n*2^n) ⌊t*(2:ℝ≥0)^n⌋₊

lemma compensatorFiniteIndex_le (n : ℕ) (t : ℝ≥0) :
    compensatorFiniteIndex n t ≤ n*2^n := min_le_left _ _

lemma compensator_cell_before_iff (n i : ℕ) (t : ℝ≥0) :
    compensatorMeshTime n (i+1) ≤ t ↔ i < ⌊t*(2:ℝ≥0)^n⌋₊ := by
  rw [compensatorMeshTime_eq_div,div_le_iff₀ (by positivity),
    ← Nat.le_floor_iff (show 0 ≤ t*(2:ℝ≥0)^n from zero_le)]
  exact Nat.succ_le_iff

lemma compensator_before_sum (n : ℕ) (t : ℝ≥0) (q : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n*2^n),
      if compensatorMeshTime n (i+1) ≤ t then q i else 0) =
    ∑ i ∈ Finset.range (compensatorFiniteIndex n t), q i := by
  simp only [compensator_cell_before_iff]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_range,compensatorFiniteIndex,lt_min_iff]

lemma compensatorFiniteIndex_eq_floor {n : ℕ} {t : ℝ≥0} (ht : t ≤ n) :
    compensatorFiniteIndex n t = ⌊t*(2:ℝ≥0)^n⌋₊ := by
  apply min_eq_right
  apply Nat.floor_le_of_le
  push_cast
  exact mul_le_mul_of_nonneg_right ht (by positivity)

lemma compensatorEndpoint_le (n : ℕ) (t : ℝ≥0) :
    compensatorMeshTime n (compensatorFiniteIndex n t) ≤ t := by
  rw [compensatorMeshTime_eq_div,div_le_iff₀ (by positivity)]
  exact (Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.floor_le (show 0 ≤ t*(2:ℝ≥0)^n from zero_le))

lemma compensatorEndpoint_lower {n : ℕ} {t : ℝ≥0} (ht : t ≤ n) :
    t < compensatorMeshTime n (compensatorFiniteIndex n t)+(2:ℝ≥0)^(-(n:ℤ)) := by
  rw [compensatorFiniteIndex_eq_floor ht,compensatorMeshTime_eq_div,
    zpow_neg,zpow_natCast,← one_div,← add_div,lt_div_iff₀ (by positivity)]
  exact Nat.lt_floor_add_one _

/-- A finite endpoint is approached from below even though the grid
horizon grows. -/
theorem compensatorEndpoint_tendsto (t : ℝ≥0) :
    Tendsto (fun n => compensatorMeshTime n (compensatorFiniteIndex n t)) atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun n : ℕ => (t:ℝ)-(2:ℝ)^(-(n:ℤ))) atTop (𝓝 (t:ℝ)) from
      by simpa only [sub_zero,zpow_neg,zpow_natCast,inv_pow] using
        tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one
          (show 0 ≤ (2:ℝ)⁻¹ by positivity) (show (2:ℝ)⁻¹<1 by norm_num)))
    tendsto_const_nhds
  · have hn : ∀ᶠ n : ℕ in atTop, t ≤ (n:ℝ≥0) :=
      (tendsto_natCast_atTop_atTop (R := ℝ≥0)).eventually (eventually_ge_atTop t)
    filter_upwards [hn] with n hn
    have h := compensatorEndpoint_lower hn
    have hc : (t:ℝ) < (compensatorMeshTime n (compensatorFiniteIndex n t):ℝ)+
        (2:ℝ)^(-(n:ℤ)) := by exact_mod_cast h
    linarith
  · exact Eventually.of_forall (fun n => by exact_mod_cast compensatorEndpoint_le n t)

def compensatorStopIndex (n : ℕ) (T : ℝ≥0∞) : ℕ :=
  if T=∞ then n*2^n else compensatorFiniteIndex n T.toNNReal

lemma compensatorStopIndex_measurable {Ω : Type*} [MeasurableSpace Ω]
    (T : Ω → ℝ≥0∞) (hT : Measurable T) (n : ℕ) :
    Measurable (fun ω => compensatorStopIndex n (T ω)) := by
  apply Measurable.ite (measurableSet_eq_fun hT measurable_const) measurable_const
  exact measurable_const.min ((hT.ennreal_toNNReal.mul_const ((2:ℝ≥0)^n)).nat_floor)

lemma compensatorStopIndex_le (n : ℕ) (T : ℝ≥0∞) :
    compensatorStopIndex n T ≤ n*2^n := by
  unfold compensatorStopIndex
  split_ifs
  · exact le_rfl
  · exact compensatorFiniteIndex_le _ _

def massAtExtendedTime (A : ℝ≥0 → ℝ) (L : ℝ) (T : ℝ≥0∞) : ℝ :=
  if T=∞ then L else A T.toNNReal

theorem massAt_compensatorEndpoint_tendsto
    (A : ℝ≥0 → ℝ) (L : ℝ) (hA : Continuous A)
    (hL : Tendsto A atTop (𝓝 L)) (T : ℝ≥0∞) :
    Tendsto (fun n => A (compensatorMeshTime n (compensatorStopIndex n T)))
      atTop (𝓝 (massAtExtendedTime A L T)) := by
  by_cases hT : T=∞
  · simpa only [compensatorStopIndex,massAtExtendedTime,hT,ite_true,
      compensatorMeshTime_end,Function.comp_def] using hL.comp (tendsto_natCast_atTop_atTop (R := ℝ≥0))
  · simpa only [compensatorStopIndex,massAtExtendedTime,hT,ite_false,Function.comp_def] using
      hA.continuousAt.tendsto.comp (compensatorEndpoint_tendsto T.toNNReal)

end SLEExactGauge

end

end OAI
