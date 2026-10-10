import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OAI

/-! The four independent samples in the alternating collar argument.  Outer
measure suffices, so no extra measurability premise is imposed on meeting events. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def pairSample (i : Fin 2) (p : X × X) : X := if i = 0 then p.1 else p.2

def crossSample (i j : Fin 2) (p : (X × X) × (Y × Y)) : X × Y :=
  (pairSample i p.1, pairSample j p.2)

theorem measurePreserving_pairSample (μ : Measure X) [IsProbabilityMeasure μ] (i : Fin 2) :
    MeasurePreserving (pairSample i) (μ.prod μ) μ := by
  fin_cases i
  · have he : pairSample (0 : Fin 2) = (Prod.fst : X × X → X) := by
      funext p
      simp [pairSample]
    change MeasurePreserving (pairSample (0 : Fin 2)) (μ.prod μ) μ
    rw [he]
    exact measurePreserving_fst
  · have he : pairSample (1 : Fin 2) = (Prod.snd : X × X → X) := by
      funext p
      simp [pairSample]
    change MeasurePreserving (pairSample (1 : Fin 2)) (μ.prod μ) μ
    rw [he]
    exact measurePreserving_snd

theorem measurePreserving_crossSample (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (i j : Fin 2) :
    MeasurePreserving (crossSample i j) ((μ.prod μ).prod (ν.prod ν)) (μ.prod ν) :=
  (measurePreserving_pairSample μ i).prod (measurePreserving_pairSample ν j)

theorem four_cross_pair_union_bound (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (R : Set (X × Y)) :
    ((μ.prod μ).prod (ν.prod ν)) {p | ∃ i j : Fin 2, crossSample i j p ∈ R} ≤
      4 * (μ.prod ν) R := by
  let M := (μ.prod μ).prod (ν.prod ν)
  have he : {p | ∃ i j : Fin 2, crossSample i j p ∈ R} =
      ⋃ i : Fin 2, ⋃ j : Fin 2, crossSample i j ⁻¹' R := by ext p; simp
  rw [he]
  calc
    M (⋃ i : Fin 2, ⋃ j : Fin 2, crossSample i j ⁻¹' R) ≤
        ∑' i : Fin 2, M (⋃ j : Fin 2, crossSample i j ⁻¹' R) := measure_iUnion_le _
    _ ≤ ∑' i : Fin 2, ∑' j : Fin 2, M (crossSample i j ⁻¹' R) :=
      ENNReal.tsum_le_tsum fun i => measure_iUnion_le _
    _ ≤ ∑' _i : Fin 2, ∑' _j : Fin 2, (μ.prod ν) R :=
      ENNReal.tsum_le_tsum fun i => ENNReal.tsum_le_tsum fun j =>
        (measurePreserving_crossSample μ ν i j).measure_preimage_le R
    _ = 4 * (μ.prod ν) R := by simp [tsum_fintype]; ring

theorem four_sample_rectangle_lower_bound (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A₀ A₁ : Set X) (B₀ B₁ : Set Y) (r : ℝ≥0∞)
    (hA₀ : r ≤ μ A₀) (hA₁ : r ≤ μ A₁) (hB₀ : r ≤ ν B₀) (hB₁ : r ≤ ν B₁) :
    r ^ 4 ≤ ((μ.prod μ).prod (ν.prod ν)) ((A₀ ×ˢ A₁) ×ˢ (B₀ ×ˢ B₁)) := by
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  calc
    r ^ 4 = (r * r) * (r * r) := by ring
    _ ≤ (μ A₀ * μ A₁) * (ν B₀ * ν B₁) :=
      mul_le_mul' (mul_le_mul' hA₀ hA₁) (mul_le_mul' hB₀ hB₁)

theorem four_sample_meeting_constraint (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A₀ A₁ : Set X) (B₀ B₁ : Set Y) (R : Set (X × Y)) (r b : ℝ≥0∞)
    (hA₀ : r ≤ μ A₀) (hA₁ : r ≤ μ A₁) (hB₀ : r ≤ ν B₀) (hB₁ : r ≤ ν B₁)
    (hcross : ∀ᵐ p ∂((μ.prod μ).prod (ν.prod ν)),
      p ∈ (A₀ ×ˢ A₁) ×ˢ (B₀ ×ˢ B₁) → ∃ i j : Fin 2, crossSample i j p ∈ R)
    (hR : (μ.prod ν) R ≤ b) : r ^ 4 ≤ 4 * b := by
  exact (four_sample_rectangle_lower_bound μ ν A₀ A₁ B₀ B₁ r hA₀ hA₁ hB₀ hB₁).trans
    ((measure_mono_ae hcross).trans ((four_cross_pair_union_bound μ ν R).trans
      (mul_le_mul' (le_refl 4) hR)))

/-- A single sufficiently small collar budget defeats the four-sample lower bound. -/
theorem exists_small_crossing_budget (C : ℝ≥0∞) (hC : C ≠ ∞) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧
      4 * (2 * δ + (1 + C) * δ ^ 2) < (1 / 10 : ℝ≥0∞) ^ 4 := by
  have hsum : (1 : ℝ≥0∞) + C ≠ ∞ := ENNReal.add_ne_top.mpr ⟨by norm_num, hC⟩
  have hc : Continuous (fun δ : ℝ≥0∞ => 4 * (2 * δ + (1 + C) * δ ^ 2)) :=
    (ENNReal.continuous_const_mul (by norm_num)).comp
      ((ENNReal.continuous_const_mul (by norm_num)).add
        ((ENNReal.continuous_const_mul hsum).comp (ENNReal.continuous_pow 2)))
  have ht : Filter.Tendsto (fun δ : ℝ≥0∞ => 4 * (2 * δ + (1 + C) * δ ^ 2))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have he := ht.eventually_lt_const (ENNReal.pow_pos (ENNReal.div_pos (by norm_num) ENNReal.ofNat_ne_top) 4 :
    (0 : ℝ≥0∞) < (1 / 10 : ℝ≥0∞) ^ 4)
  have hp : ∀ᶠ δ : ℝ≥0∞ in nhdsWithin 0 (Ioi 0), 0 < δ := self_mem_nhdsWithin
  exact (hp.and he).exists

end CircleDomainRigidity

end

end OAI
