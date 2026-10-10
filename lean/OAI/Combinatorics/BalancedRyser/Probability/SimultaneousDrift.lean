import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.Combinatorics.BalancedRyser.Probability.BoundedDrift

namespace OAI

open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators Topology

namespace Balanced
open scoped _root_.Balanced

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem simultaneous_bounded_drift [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] (ℱ : Filtration ℕ mΩ) (X : ι → ℕ → Ω → ℝ)
    {T : ℕ} {L u : ℝ} (hT : 1 ≤ T) (hL : 0 < L) (hu : 0 < u)
    (hX : ∀ i j, j ≤ T → StronglyMeasurable[ℱ j] (X i j))
    (hb : ∀ i j, j < T → ∀ᵐ ω ∂μ, |X i (j + 1) ω - X i j ω| ≤ L) :
    μ.real {ω | ∃ i, ∃ t ≤ T,
      u ≤ |X i t ω - X i 0 ω - ∑ j ∈ Finset.range t,
        μ[fun ω ↦ X i (j + 1) ω - X i j ω | ℱ j] ω|} ≤
      2 * (Fintype.card ι : ℝ) * (T + 1 : ℕ) * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
  classical
  let E : ι × Fin (T + 1) → Set Ω := fun p ↦ {ω |
    u ≤ |X p.1 p.2 ω - X p.1 0 ω - ∑ j ∈ Finset.range p.2,
      μ[fun ω ↦ X p.1 (j + 1) ω - X p.1 j ω | ℱ j] ω|}
  have hset : {ω | ∃ i, ∃ t ≤ T,
      u ≤ |X i t ω - X i 0 ω - ∑ j ∈ Finset.range t,
        μ[fun ω ↦ X i (j + 1) ω - X i j ω | ℱ j] ω|} ⊆ ⋃ p, E p := by
    rintro ω ⟨i, t, ht, hω⟩
    exact Set.mem_iUnion.mpr ⟨(i, ⟨t, by omega⟩), hω⟩
  calc
    _ ≤ μ.real (⋃ p, E p) := measureReal_mono hset
    _ ≤ ∑ p, μ.real (E p) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _p : ι × Fin (T + 1), 2 * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact boundedDriftConcentration_proof μ ℱ (X p.1) T L hT hL
        (hX p.1) (hb p.1) u hu p.2 (by omega)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]; ring

noncomputable def predictableDriftSum (μ : Measure Ω) (ℱ : Filtration ℕ mΩ)
    (X : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range t, μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω

section OneSided

variable [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
    {T t : ℕ} {L u D : ℝ}
    (hT : 1 ≤ T) (hL : 0 < L) (hu : 0 < u) (ht : t ≤ T)
    (hX : ∀ j ≤ T, StronglyMeasurable[ℱ j] (X j))
    (hb : ∀ j < T, ∀ᵐ ω ∂μ, |X (j + 1) ω - X j ω| ≤ L)

include hT hL hu ht hX hb

theorem upper_tail_of_drift_le
    (hd : ∀ᵐ ω ∂μ, predictableDriftSum μ ℱ X t ω ≤ D) :
    μ.real {ω | D + u ≤ X t ω - X 0 ω} ≤
      2 * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
  have htail := boundedDriftConcentration_proof μ ℱ X T L hT hL hX hb u hu t ht
  apply le_trans ?_ htail
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono_ae
  filter_upwards [hd] with ω hω
  intro he
  change D + u ≤ X t ω - X 0 ω at he
  change u ≤ |X t ω - X 0 ω - predictableDriftSum μ ℱ X t ω|
  exact (by linarith : u ≤ X t ω - X 0 ω - predictableDriftSum μ ℱ X t ω).trans
    (le_abs_self _)

theorem lower_tail_of_le_drift
    (hd : ∀ᵐ ω ∂μ, D ≤ predictableDriftSum μ ℱ X t ω) :
    μ.real {ω | X t ω - X 0 ω ≤ D - u} ≤
      2 * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
  have htail := boundedDriftConcentration_proof μ ℱ X T L hT hL hX hb u hu t ht
  apply le_trans ?_ htail
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono_ae
  filter_upwards [hd] with ω hω
  intro he
  change X t ω - X 0 ω ≤ D - u at he
  change u ≤ |X t ω - X 0 ω - predictableDriftSum μ ℱ X t ω|
  exact (by linarith : u ≤ -(X t ω - X 0 ω - predictableDriftSum μ ℱ X t ω)).trans
    (neg_le_abs _)

theorem abs_tail_of_abs_drift_le
    (hd : ∀ᵐ ω ∂μ, |predictableDriftSum μ ℱ X t ω| ≤ D) :
    μ.real {ω | D + u ≤ |X t ω - X 0 ω|} ≤
      2 * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2)) := by
  have htail := boundedDriftConcentration_proof μ ℱ X T L hT hL hX hb u hu t ht
  apply le_trans ?_ htail
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono_ae
  filter_upwards [hd] with ω hω
  intro he
  change D + u ≤ |X t ω - X 0 ω| at he
  change u ≤ |X t ω - X 0 ω - predictableDriftSum μ ℱ X t ω|
  have htri := abs_add_le (X t ω - X 0 ω - predictableDriftSum μ ℱ X t ω)
    (predictableDriftSum μ ℱ X t ω)
  simp only [sub_add_cancel] at htri
  linarith

end OneSided

theorem selection_azuma_exponent {q C : ℝ} (hq : 0 < q) (hC : 0 < C) :
    (q ^ ((4 : ℝ) / 5) / 2) ^ 2 /
      (8 * (3 * q) * (C * q ^ ((1 : ℝ) / 8)) ^ 2) =
      q ^ ((7 : ℝ) / 20) / (96 * C ^ 2) := by
  have h80 : (q ^ ((4 : ℝ) / 5)) ^ 2 = q ^ ((8 : ℝ) / 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    norm_num
  have h18 : (q ^ ((1 : ℝ) / 8)) ^ 2 = q ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    norm_num
  have hfactor : q ^ ((8 : ℝ) / 5) = q ^ ((7 : ℝ) / 20) * q * q ^ ((1 : ℝ) / 4) := by
    calc
      _ = q ^ (((7 : ℝ) / 20 + 1) + (1 : ℝ) / 4) := by norm_num
      _ = _ := by rw [Real.rpow_add hq, Real.rpow_add hq, Real.rpow_one]
  have hqp : q ^ ((1 : ℝ) / 4) ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  rw [div_pow, mul_pow, h80, h18, hfactor]
  field_simp
  ring

theorem tendsto_nat_pow_mul_exp_neg_rpow (m : ℕ) {r c : ℝ}
    (hr : 0 < r) (hc : 0 < c) :
    Tendsto (fun q : ℕ ↦ (q : ℝ) ^ m * exp (-c * (q : ℝ) ^ r)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((m : ℝ) / r) c hc).comp
    ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop)
  convert h using 1
  funext q
  congr 1
  change (q : ℝ) ^ m = ((q : ℝ) ^ r) ^ ((m : ℝ) / r)
  have he : r * ((m : ℝ) / r) = (m : ℝ) := by field_simp
  rw [← Real.rpow_mul (Nat.cast_nonneg q), he, Real.rpow_natCast]

theorem tendsto_selection_simultaneous_error (A : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun q : ℕ ↦ A * (q : ℝ) ^ 3 * exp (-c * (q : ℝ) ^ ((7 : ℝ) / 20)))
      atTop (𝓝 0) := by
  simpa only [mul_zero, mul_assoc] using
    (tendsto_nat_pow_mul_exp_neg_rpow 3 (by norm_num : 0 < (7 : ℝ) / 20) hc).const_mul A

end Balanced

end OAI
