import OAI.NumberTheory.JointDickman.Arithmetic.PrimeLogIntervals
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # The finite measure of logarithmic large-prime locations -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

noncomputable def finiteDirac (t : ℝ) : FiniteMeasure ℝ :=
  ⟨Measure.dirac t, inferInstance⟩

noncomputable def primeLogMeasure (c x : ℝ) : FiniteMeasure ℝ :=
  ∑ p ∈ largePrimeSet x (x^c),
    (Real.toNNReal (1/(p : ℝ))) • finiteDirac (Real.log p/Real.log x)

open Classical in
theorem primeLogMeasure_apply (c x : ℝ) (s : Set ℝ) :
    ((primeLogMeasure c x) s : ℝ) =
      ∑ p ∈ largePrimeSet x (x^c),
        if Real.log p/Real.log x ∈ s then 1/(p : ℝ) else 0 := by
  classical
  unfold primeLogMeasure
  induction largePrimeSet x (x^c) using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    simp only [sum_insert hp, FiniteMeasure.coeFn_add, Pi.add_apply,
      NNReal.coe_add, FiniteMeasure.smul_apply, smul_eq_mul, NNReal.coe_mul, ih]
    congr 1
    by_cases h : Real.log p/Real.log x ∈ s <;>
      simp [finiteDirac, Measure.dirac_apply, h]

theorem logPrimeLocation_mem_Ioc {x : ℝ} (hx : 1 < x) {p : ℕ}
    (hp : 0 < p) (a b : ℝ) :
    Real.log p/Real.log x ∈ Set.Ioc a b ↔ x^a < p ∧ (p : ℝ) ≤ x^b := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 < Real.log x := Real.log_pos hx
  rw [Set.mem_Ioc, lt_div_iff₀ hlog, div_le_iff₀ hlog]
  constructor
  · rintro ⟨ha,hb⟩
    constructor
    · apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hx0 a) hp0).mp
      simpa only [Real.log_rpow hx0, mul_comm] using ha
    · apply (Real.log_le_log_iff hp0 (Real.rpow_pos_of_pos hx0 b)).mp
      simpa only [Real.log_rpow hx0, mul_comm] using hb
  · rintro ⟨ha,hb⟩
    constructor
    · have := (Real.log_lt_log_iff (Real.rpow_pos_of_pos hx0 a) hp0).mpr ha
      simpa only [Real.log_rpow hx0, mul_comm] using this
    · have := (Real.log_le_log_iff hp0 (Real.rpow_pos_of_pos hx0 b)).mpr hb
      simpa only [Real.log_rpow hx0, mul_comm] using this

theorem primeLogMeasure_Ioc {c x a b : ℝ} (hx : 1 < x)
    (hca : c ≤ a) (hb : b ≤ 1) :
    ((primeLogMeasure c x) (Set.Ioc a b) : ℝ) =
      ∑ p ∈ largePrimeSet (x^b) (x^a), 1/(p : ℝ) := by
  classical
  rw [primeLogMeasure_apply]
  trans ∑ p ∈ (largePrimeSet x (x^c)).filter (fun p : ℕ => Real.log p/Real.log x ∈ Set.Ioc a b), 1/(p : ℝ)
  · symm
    convert sum_filter (s := largePrimeSet x (x^c)) (p := fun p : ℕ => Real.log p/Real.log x ∈ Set.Ioc a b) (f := fun p => 1/(p : ℝ)) using 1
    congr 3
    funext p
    split_ifs <;> rfl
  apply sum_congr
  · ext p
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hcb : x^c ≤ x^a := Real.rpow_le_rpow_of_exponent_le hx.le hca
    have hbx : x^b ≤ x := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx.le hb
    simp only [mem_filter, largePrimeSet, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨⟨hpN,hp⟩,hpc⟩,hloc⟩
      obtain ⟨hpa,hpb⟩ := (logPrimeLocation_mem_Ioc hx hp.pos a b).mp hloc
      exact ⟨⟨Nat.le_floor hpb,hp⟩,hpa⟩
    · rintro ⟨⟨hpN,hp⟩,hpa⟩
      have hpb : (p : ℝ) ≤ x^b := (Nat.le_floor_iff (Real.rpow_nonneg hx0.le b)).mp hpN
      exact ⟨⟨⟨Nat.le_floor (hpb.trans hbx),hp⟩,hcb.trans_lt hpa⟩,
        (logPrimeLocation_mem_Ioc hx hp.pos a b).mpr ⟨hpa,hpb⟩⟩
  · intros; rfl

theorem primeLogMeasure_interval_tendsto {c a b : ℝ}
    (ha : 0 < a) (hca : c ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun x => ((primeLogMeasure c x) (Set.Ioc a b) : ℝ))
      atTop (𝓝 (Real.log b-Real.log a)) := by
  apply (prime_power_interval_tendsto ha hab).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (primeLogMeasure_Ioc hx hca hb).symm

noncomputable def logIntervalVolume (c : ℝ) : FiniteMeasure ℝ :=
  ⟨volume.restrict (Set.Ioc (Real.log c) 0), inferInstance⟩

noncomputable def logarithmicPrimeMeasure (c : ℝ) : FiniteMeasure ℝ :=
  (logIntervalVolume c).map Real.exp

theorem logarithmicPrimeMeasure_Ioc {c a b : ℝ}
    (hc : 0 < c) (hca : c ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ((logarithmicPrimeMeasure c) (Set.Ioc a b) : ℝ) = Real.log b-Real.log a := by
  have ha : 0 < a := hc.trans_le hca
  have hb0 : 0 < b := ha.trans_le hab
  have hpre : Real.exp ⁻¹' Set.Ioc a b = Set.Ioc (Real.log a) (Real.log b) := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioc, ← Real.log_lt_iff_lt_exp ha,
      ← Real.le_log_iff_exp_le hb0]
  have hsub : Set.Ioc (Real.log a) (Real.log b) ⊆ Set.Ioc (Real.log c) 0 := by
    intro t ht
    exact ⟨(Real.log_le_log hc hca).trans_lt ht.1,
      ht.2.trans (Real.log_nonpos hb0.le hb)⟩
  rw [logarithmicPrimeMeasure, FiniteMeasure.map_apply _ Real.measurable_exp measurableSet_Ioc,
    hpre, logIntervalVolume, FiniteMeasure.mk_apply, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.mpr hsub, Real.volume_Ioc]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr (Real.log_le_log ha hab))

end JointDickman

end OAI
