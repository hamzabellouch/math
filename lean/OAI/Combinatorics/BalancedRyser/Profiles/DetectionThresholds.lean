import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Inv
import Mathlib.Tactic.Measurability
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

namespace OAI

open MeasureTheory Filter Set
open scoped Topology

namespace Balanced.ProfileDetection

def cutoffDetection {Ω : Type*} (z h : Ω → ℝ) (n : ℕ) : Set Ω :=
  {x | 1 / ((n : ℝ) + 1) < z x ∧ z x < 1 ∧ 3 / ((n : ℝ) + 1) < |h x|}

def positiveDetection {Ω : Type*} (z h : Ω → ℝ) : Set Ω :=
  {x | 0 < z x ∧ z x < 1 ∧ h x ≠ 0}

theorem cutoffDetection_mono {Ω : Type*} (z h : Ω → ℝ) :
    Monotone (cutoffDetection z h) := by
  intro n m hnm x hx
  have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine ⟨lt_of_le_of_lt ?_ hx.1, hx.2.1, lt_of_le_of_lt ?_ hx.2.2⟩
  · exact div_le_div_of_nonneg_left (by norm_num) hn hnm'
  · exact div_le_div_of_nonneg_left (by norm_num) hn hnm'

theorem iUnion_cutoffDetection {Ω : Type*} (z h : Ω → ℝ) :
    (⋃ n : ℕ, cutoffDetection z h n) = positiveDetection z h := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    refine ⟨lt_trans (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) hn.1,
      hn.2.1, ?_⟩
    exact abs_pos.mp (lt_trans (by positivity : (0 : ℝ) < 3 / ((n : ℝ) + 1)) hn.2.2)
  · intro hx
    have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hz : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < z x :=
      (tendsto_order.mp hseq).2 _ hx.1
    have hh : ∀ᶠ n : ℕ in atTop, 3 / ((n : ℝ) + 1) < |h x| := by
      have ht := hseq.const_mul 3
      simp only [mul_zero] at ht
      have hb := (tendsto_order.mp ht).2 _ (abs_pos.mpr hx.2.2)
      simpa only [mul_one_div] using hb
    obtain ⟨n, hnz, hnh⟩ := (hz.and hh).exists
    exact mem_iUnion.mpr ⟨n, hnz, hx.2.1, hnh⟩

theorem tendsto_measure_cutoffDetection {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (z h : Ω → ℝ) :
    Tendsto (fun n : ℕ => μ (cutoffDetection z h n)) atTop
      (𝓝 (μ (positiveDetection z h))) := by
  have ht := tendsto_measure_iUnion_atTop (μ := μ) (cutoffDetection_mono z h)
  simpa only [Function.comp_def, iUnion_cutoffDetection] using ht

theorem tendsto_measureReal_cutoffDetection {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (z h : Ω → ℝ) :
    Tendsto (fun n : ℕ => μ.real (cutoffDetection z h n)) atTop
      (𝓝 (μ.real (positiveDetection z h))) := by
  exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp
    (tendsto_measure_cutoffDetection μ z h)

theorem product_positiveDetection_mass {A : Type*} [MeasurableSpace A]
    (ν : Measure A) (τ : Measure ℝ) [IsProbabilityMeasure τ]
    (V : Set A) (hV : MeasurableSet V) (h : A × ℝ → ℝ) (hh : Measurable h)
    (hparam : ∀ᵐ z : ℝ ∂τ, z ∈ Ioo 0 1)
    (hvisible : ∀ x ∈ V, ∀ᵐ z : ℝ ∂τ, h (x, z) ≠ 0)
    (hinvisible : ∀ x ∉ V, ∀ᵐ z : ℝ ∂τ, h (x, z) = 0) :
    (ν.prod τ) (positiveDetection Prod.snd h) = ν V := by
  have hD : MeasurableSet (positiveDetection Prod.snd h) := by
    unfold positiveDetection
    measurability
  have hM : MeasurableSet {p : A × ℝ |
      (p ∈ positiveDetection Prod.snd h ↔ p.1 ∈ V)} := by
    exact hD.iff (hV.preimage measurable_fst)
  have hAE : ∀ᵐ p : A × ℝ ∂ν.prod τ,
      p ∈ positiveDetection Prod.snd h ↔ p.1 ∈ V := by
    apply (Measure.ae_prod_iff_ae_ae hM).mpr
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ V
    · filter_upwards [hparam, hvisible x hx] with z hz hn
      simp only [positiveDetection, mem_ofPred_eq, hx, iff_true]
      exact ⟨hz.1, hz.2, hn⟩
    · filter_upwards [hinvisible x hx] with z hz
      simp [positiveDetection, hx, hz]
  calc
    (ν.prod τ) (positiveDetection Prod.snd h) = (ν.prod τ) (V ×ˢ (univ : Set ℝ)) := by
      apply measure_congr
      filter_upwards [hAE] with p hp
      apply propext
      change (p ∈ positiveDetection Prod.snd h ↔ p.1 ∈ V ∧ p.2 ∈ (univ : Set ℝ))
      simpa only [mem_univ, and_true] using hp
    _ = ν V := by rw [Measure.prod_prod]; simp

theorem tendsto_cutoffDetection_visible_mass {A : Type*} [MeasurableSpace A]
    (ν : Measure A) (τ : Measure ℝ) [IsProbabilityMeasure τ]
    (V : Set A) (hV : MeasurableSet V) (h : A × ℝ → ℝ) (hh : Measurable h)
    (hparam : ∀ᵐ z : ℝ ∂τ, z ∈ Ioo 0 1)
    (hvisible : ∀ x ∈ V, ∀ᵐ z : ℝ ∂τ, h (x, z) ≠ 0)
    (hinvisible : ∀ x ∉ V, ∀ᵐ z : ℝ ∂τ, h (x, z) = 0) :
    Tendsto (fun n : ℕ => (ν.prod τ) (cutoffDetection Prod.snd h n)) atTop
      (𝓝 (ν V)) := by
  have ht := tendsto_measure_cutoffDetection (ν.prod τ) Prod.snd h
  rwa [product_positiveDetection_mass ν τ V hV h hh hparam hvisible hinvisible] at ht

end Balanced.ProfileDetection

end OAI
