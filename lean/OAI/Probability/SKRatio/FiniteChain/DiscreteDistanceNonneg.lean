import Mathlib
import OAI.Probability.SKRatio.FiniteChain.Spin

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter
namespace SKRatio
section MixingTime
variable {n : ℕ}

theorem discreteDistance_nonneg (g : Disorder n) (k : ℕ) :
    0 ≤ discreteDistance g k :=
  (totalVariation_nonneg _ _).trans (tv_le_discreteDistance g k (fun _ => true))

theorem discreteDistance_le_one (g : Disorder n) (k : ℕ) :
    discreteDistance g k ≤ 1 := by
  apply Finset.sup'_le
  intro x _
  have hP := transition_pow_stochastic g k
  exact totalVariation_le_one _ _ (hP.1 x) (mass_nonneg g 0)
    (Matrix.sum_row_of_mem_rowStochastic hP x) (sum_mass g 0)

theorem discreteDistance_antitone (g : Disorder n) : Antitone (discreteDistance g) := by
  apply antitone_nat_of_succ_le
  intro k
  apply Finset.sup'_le
  intro x _
  have hsum : (∑ y, (transition g ^ k) x y) = ∑ y, mass g 0 y := by
    rw [Matrix.sum_row_of_mem_rowStochastic (transition_pow_stochastic g k), sum_mass]
  calc
    totalVariation ((transition g ^ (k + 1)) x) (mass g 0) =
        totalVariation ((transition g ^ k) x ᵥ* transition g) (mass g 0 ᵥ* transition g) := by
      rw [pow_succ, Matrix.mul_apply_eq_vecMul, transition_stationary]
    _ ≤ totalVariation ((transition g ^ k) x) (mass g 0) :=
      totalVariation_contract _ (transition_stochastic g) _ _ hsum
    _ ≤ discreteDistance g k := tv_le_discreteDistance g k x

theorem exists_geometric_bound (g : Disorder n) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ k : ℕ, discreteDistance g (n * k) ≤ r ^ k := by
  obtain ⟨r, hr0, hr1, hbound⟩ := exists_geometric_block_bound
    (transition g) (transition_stochastic g) (mass g 0) (mass_nonneg g 0) (sum_mass g 0)
    n (transition_n_pos g) (transition_pow_stationary g n)
  refine ⟨r, hr0, hr1, fun k => Finset.sup'_le _ _ (fun x _ => hbound k x)⟩

theorem exists_mixing_time (g : Disorder n) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, discreteDistance g k ≤ ε := by
  obtain ⟨r, hr0, hr1, hbound⟩ := exists_geometric_bound g
  have H := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).eventually (gt_mem_nhds hε)
  obtain ⟨k, hk⟩ := H.exists
  exact ⟨n * k, (hbound k).trans hk.le⟩

theorem mixingTime_spec (g : Disorder n) {ε : ℝ} (hε : 0 < ε) :
    discreteDistance g (mixingTime g ε) ≤ ε :=
  Nat.sInf_mem (exists_mixing_time g hε)

theorem mixingTime_le_of_distance_le (g : Disorder n) {ε : ℝ} {k : ℕ}
    (hk : discreteDistance g k ≤ ε) : mixingTime g ε ≤ k := Nat.sInf_le hk

theorem mixingTime_le_iff (g : Disorder n) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    mixingTime g ε ≤ k ↔ discreteDistance g k ≤ ε := by
  constructor
  · intro h
    exact (discreteDistance_antitone g h).trans (mixingTime_spec g hε)
  · exact mixingTime_le_of_distance_le g

theorem lt_mixingTime_of_lt_distance (g : Disorder n) {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (hk : ε < discreteDistance g k) : k < mixingTime g ε := by
  exact lt_of_not_ge (fun h => not_le_of_gt hk ((mixingTime_le_iff g hε k).mp h))

theorem discreteDistance_zero_lower (g : Disorder n) :
    1 - (1 / 2 : ℝ) ^ n ≤ discreteDistance g 0 := by
  have hpoint (x : Spin n) : 1 - mass g 0 x ≤ discreteDistance g 0 := by
    have h := tv_le_discreteDistance g 0 x
    simpa only [pow_zero, totalVariation_dirac _ (mass_nonneg g 0) (sum_mass g 0)] using h
  have hsum : (Fintype.card (Spin n) : ℝ) * (1 - discreteDistance g 0) ≤ 1 := by
    calc
      (Fintype.card (Spin n) : ℝ) * (1 - discreteDistance g 0) =
          ∑ _x : Spin n, (1 - discreteDistance g 0) := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ x, mass g 0 x := Finset.sum_le_sum (fun x _ => by linarith [hpoint x])
      _ = 1 := sum_mass g 0
  have hcard : Fintype.card (Spin n) = 2 ^ n := by simp [Spin]
  have hcpos : (0 : ℝ) < Fintype.card (Spin n) := Nat.cast_pos.mpr Fintype.card_pos
  have h : 1 - discreteDistance g 0 ≤ (1 : ℝ) / Fintype.card (Spin n) :=
    (le_div_iff₀ hcpos).mpr (by simpa only [mul_comm] using hsum)
  have hid : (1 : ℝ) / Fintype.card (Spin n) = (1 / 2 : ℝ) ^ n := by
    rw [hcard, Nat.cast_pow, Nat.cast_ofNat, one_div_pow]
  rw [hid] at h
  linarith

theorem denominator_eventually_positive (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1 - ε) := by
  have H := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).eventually
    (gt_mem_nhds hε0)
  filter_upwards [H] with n hn
  intro g
  apply lt_mixingTime_of_lt_distance g (sub_pos.mpr hε1)
  linarith [discreteDistance_zero_lower g]

theorem mixing_ratio_bound (g : Disorder n) {ε b T : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hb0 : 0 < b) (hb1 : b < 1) (hT : 0 < T)
    (hlower : 1 - ε < discreteDistance g ⌊(1 - b) * T⌋₊)
    (hupper : discreteDistance g ⌈(1 + b) * T⌉₊ ≤ ε) :
    (mixingTime g ε : ℝ) / (mixingTime g (1 - ε) : ℝ) ≤
      (1 + b) / (1 - b) + 1 / ((1 - b) * T) := by
  have hlo := lt_mixingTime_of_lt_distance g (sub_pos.mpr hε1) hlower
  have hup := (mixingTime_le_iff g hε0 _).mpr hupper
  have htlo : (1 - b) * T < (mixingTime g (1 - ε) : ℝ) := by
    have hcast : (⌊(1 - b) * T⌋₊ : ℝ) + 1 ≤ (mixingTime g (1 - ε) : ℝ) := by
      exact_mod_cast hlo
    exact (Nat.lt_floor_add_one _).trans_le hcast
  have hthi : (mixingTime g ε : ℝ) ≤ (1 + b) * T + 1 := by
    have hcast : (mixingTime g ε : ℝ) ≤ (⌈(1 + b) * T⌉₊ : ℝ) := by
      exact_mod_cast hup
    exact hcast.trans (Nat.ceil_lt_add_one (by positivity)).le
  have htpos : 0 < (1 - b) * T := mul_pos (sub_pos.mpr hb1) hT
  have hden : 0 < (mixingTime g (1 - ε) : ℝ) := htpos.trans htlo
  calc
    (mixingTime g ε : ℝ) / (mixingTime g (1 - ε) : ℝ) ≤
        ((1 + b) * T + 1) / (mixingTime g (1 - ε) : ℝ) :=
      div_le_div_of_nonneg_right hthi hden.le
    _ ≤ ((1 + b) * T + 1) / ((1 - b) * T) :=
      div_le_div_of_nonneg_left (by positivity) htpos htlo.le
    _ = (1 + b) / (1 - b) + 1 / ((1 - b) * T) := by
      field_simp

end MixingTime

section Measurability
variable {n : ℕ}

@[fun_prop] theorem continuous_coupling (i j : Fin n) :
    Continuous (fun g : Disorder n => coupling g i j) := by
  unfold coupling
  split_ifs <;> fun_prop

@[fun_prop] theorem continuous_hamiltonian (h : Fin n → ℝ) (x : Spin n) :
    Continuous (fun g : Disorder n => hamiltonian g h x) := by
  unfold hamiltonian
  fun_prop

@[fun_prop] theorem continuous_weight (h : Fin n → ℝ) (x : Spin n) :
    Continuous (fun g : Disorder n => weight g h x) := by
  unfold weight
  fun_prop

@[fun_prop] theorem continuous_partition (h : Fin n → ℝ) :
    Continuous (fun g : Disorder n => partition g h) := by
  unfold partition
  fun_prop

@[fun_prop] theorem continuous_mass (h : Fin n → ℝ) (x : Spin n) :
    Continuous (fun g : Disorder n => mass g h x) := by
  exact (continuous_weight h x).div (continuous_partition h)
    (fun g => (partition_pos g h).ne')

@[fun_prop] theorem continuous_siteKernel (i : Fin n) (x y : Spin n) :
    Continuous (fun g : Disorder n => siteKernel g i x y) := by
  have hd : ∀ g : Disorder n, mass g 0 x + mass g 0 (flip i x) ≠ 0 :=
    fun g => (add_pos (mass_pos g 0 x) (mass_pos g 0 (flip i x))).ne'
  have hx := (continuous_mass 0 x).div
    ((continuous_mass 0 x).add (continuous_mass 0 (flip i x))) hd
  have hf := (continuous_mass 0 (flip i x)).div
    ((continuous_mass 0 x).add (continuous_mass 0 (flip i x))) hd
  unfold siteKernel
  split_ifs <;> fun_prop

@[fun_prop] theorem continuous_transition (x y : Spin n) :
    Continuous (fun g : Disorder n => transition g x y) := by
  by_cases hn : n = 0
  · simp only [transition, hn, ↓reduceIte]
    fun_prop
  · simp only [transition, hn, ↓reduceIte]
    fun_prop

@[fun_prop] theorem continuous_transition_pow (k : ℕ) (x y : Spin n) :
    Continuous (fun g : Disorder n => (transition g ^ k) x y) := by
  induction k generalizing x y with
  | zero => simp only [pow_zero]; fun_prop
  | succ k ih =>
    simp only [pow_succ, Matrix.mul_apply]
    fun_prop

@[fun_prop] theorem continuous_discreteDistance (k : ℕ) :
    Continuous (fun g : Disorder n => discreteDistance g k) := by
  have h : Continuous (Finset.univ.sup' Finset.univ_nonempty
      (fun (x : Spin n) (g : Disorder n) =>
        totalVariation ((transition g ^ k) x) (mass g 0))) := by
    apply Continuous.finset_sup'
    intro x _
    unfold totalVariation
    fun_prop
  exact h.congr (fun g => Finset.sup'_apply _ _ g)

@[fun_prop] theorem measurable_mixingTime {ε : ℝ} (hε : 0 < ε) :
    Measurable (fun g : Disorder n => mixingTime g ε) := by
  apply measurable_of_Iic
  intro k
  have heq : (fun g : Disorder n => mixingTime g ε) ⁻¹' Set.Iic k =
      {g : Disorder n | discreteDistance g k ≤ ε} := by
    ext g
    exact mixingTime_le_iff g hε k
  rw [heq]
  exact measurableSet_le (continuous_discreteDistance k).measurable measurable_const

theorem measurableSet_ratio_event {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (η : ℝ) :
    MeasurableSet {g : Disorder n | 1 + η <
      (mixingTime g ε : ℝ) / (mixingTime g (1 - ε) : ℝ)} := by
  have hm1 := measurable_mixingTime (n := n) hε0
  have hm2 := measurable_mixingTime (n := n) (sub_pos.mpr hε1)
  apply measurableSet_lt measurable_const
  fun_prop

end Measurability

end SKRatio

noncomputable section
open scoped BigOperators Topology Matrix
open MeasureTheory ProbabilityTheory Filter

end
end
end

end OAI
