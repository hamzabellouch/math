import Mathlib
import OAI.Analysis.HardSphere.Bridges.Index

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.Wiener

def moment8 : ℝ≥0∞ := (eLpNorm (id : ℝ → ℝ) 8 (gaussianReal 0 1)) ^ 8

lemma moment8_ne_top : moment8 ≠ ∞ :=
  ENNReal.pow_ne_top (memLp_id_gaussianReal' (μ := 0) (v := 1) 8 (by norm_num)).ne

lemma coordinate_tail8 (i : Index) {a : ℝ} (ha : 0 < a) :
    law {ω | a ≤ |ω i|} ≤ (ENNReal.ofReal a)⁻¹ ^ (8 : ℕ) * moment8 := by
  have hm := memLp_id_gaussianReal' (μ := 0) (v := 1) 8 (by norm_num)
  have he : eLpNorm (fun ω : Noise ↦ ω i) 8 law =
      eLpNorm (id : ℝ → ℝ) 8 (gaussianReal 0 1) := by
    simpa only [Function.comp_def, id_eq] using
      (eLpNorm_comp_measurePreserving (p := 8) (g := (id : ℝ → ℝ))
        hm.aestronglyMeasurable (coordinate_preserving i))
  have ht := meas_ge_le_mul_pow_eLpNorm_enorm law (p := 8) (by norm_num) (by norm_num)
    (f := fun noise : Noise ↦ noise i)
    (ε := ENNReal.ofReal a) (ne_of_gt (ENNReal.ofReal_pos.mpr ha)) (by simp)
  have hs : {ω : Noise | ENNReal.ofReal a ≤ ‖ω i‖ₑ} = {ω | a ≤ |ω i|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)
  simpa only [Function.comp_def, id_eq, ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast,
    Nat.cast_ofNat, he, hs, moment8] using ht

def normMultiplier : ℝ := 1 + ∑' n : ℕ, amplitude n * (4/3:ℝ)^n

lemma normMultiplier_pos : 0 < normMultiplier := by
  have h : 0 ≤ ∑' n : ℕ, amplitude n * (4/3:ℝ)^n :=
    tsum_nonneg fun n ↦ mul_nonneg (amplitude_nonneg n) (by positivity)
  unfold normMultiplier
  linarith

lemma norm_path_of_coordinate_bounds (ω : Noise) {B : ℝ} (hB : 0 ≤ B)
    (h0 : |ω (.inl ())| ≤ B)
    (h : ∀ n k, |ω (.inr ⟨n,k⟩)| ≤ B*(4/3:ℝ)^n) :
    ‖path ω‖ ≤ B*normMultiplier := by
  have hn : ‖(⟨fun t : Time ↦ t.val, continuous_subtype_val⟩ : C(Time,ℝ))‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ (by norm_num : (0:ℝ)≤1)).2
    intro t
    simpa only [ContinuousMap.coe_mk,Real.norm_eq_abs,abs_of_nonneg t.property.1] using t.property.2
  have ht : ‖∑' n, level n ω‖ ≤ B*(∑' n : ℕ, amplitude n*(4/3:ℝ)^n) := by
    apply tsum_of_norm_bounded (summable_level_bound.hasSum.mul_left B)
    intro n
    exact (norm_level_le n ω (mul_nonneg hB (by positivity)) (h n)).trans_eq (by ring)
  calc
    ‖path ω‖ ≤ ‖ω (.inl ()) • (⟨fun t : Time ↦ t.val, continuous_subtype_val⟩ : C(Time,ℝ))‖ + ‖∑' n, level n ω‖ := norm_add_le _ _
    _ ≤ B*1+B*(∑' n : ℕ, amplitude n*(4/3:ℝ)^n) := by
      apply add_le_add _ ht
      rw [norm_smul]
      exact mul_le_mul h0 hn (norm_nonneg _) hB
    _ = B*normMultiplier := by unfold normMultiplier; ring

lemma scaled_badLevel_bound (n : ℕ) {B : ℝ} (hB : 0 < B) :
    law {ω | ∃ k : Fin (2^n), B*(4/3:ℝ)^n ≤ |ω (.inr ⟨n,k⟩)|} ≤
      (ENNReal.ofReal B)⁻¹^8 * ((2:ℝ≥0∞)*(4/3)⁻¹^8)^n * moment8 := by
  have hu : {ω : Noise | ∃ k : Fin (2^n), B*(4/3:ℝ)^n ≤ |ω (.inr ⟨n,k⟩)|} =
      ⋃ k : Fin (2^n), {ω | B*(4/3:ℝ)^n ≤ |ω (.inr ⟨n,k⟩)|} := by ext ω; simp
  rw [hu]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  calc
    _ ≤ ∑ _k : Fin (2^n), (ENNReal.ofReal (B*(4/3:ℝ)^n))⁻¹^8*moment8 :=
      Finset.sum_le_sum fun k _ ↦ coordinate_tail8 _ (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat, ENNReal.ofReal_mul hB.le,
        ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤4/3),
        ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3), ENNReal.ofReal_ofNat]
      rw [ENNReal.mul_inv (Or.inl (by simpa using hB)) (Or.inl ENNReal.ofReal_ne_top),
        mul_pow, ENNReal.inv_pow, ← pow_mul, Nat.mul_comm n 8, pow_mul]
      simp only [mul_pow]
      ring

lemma norm_wiener_tail8 {B : ℝ} (hB : 0 < B) :
    wiener {w | B*normMultiplier < ‖w‖} ≤
      (ENNReal.ofReal B)⁻¹^8 *
        ((1+ (1-(2:ℝ≥0∞)*(4/3)⁻¹^8)⁻¹)*moment8) := by
  rw [wiener,Measure.map_apply measurable_path (measurableSet_lt measurable_const measurable_norm)]
  have hsub : path ⁻¹' {w | B*normMultiplier < ‖w‖} ⊆
      {ω | B≤|ω (.inl ())|} ∪
        ⋃ n : ℕ, {ω | ∃ k : Fin (2^n), B*(4/3:ℝ)^n ≤ |ω (.inr ⟨n,k⟩)|} := by
    intro ω hω
    by_contra hc
    have hc' := not_or.mp hc
    have h0 : |ω (.inl ())| ≤ B := (lt_of_not_ge hc'.1).le
    have hn : ∀ n k, |ω (.inr ⟨n,k⟩)| ≤ B*(4/3:ℝ)^n := by
      intro n k
      by_contra hh
      apply hc'.2
      exact Set.mem_iUnion.mpr ⟨n,⟨k,(lt_of_not_ge hh).le⟩⟩
    exact (not_lt_of_ge (norm_path_of_coordinate_bounds ω hB.le h0 hn)) hω
  calc
    _ ≤ law ({ω | B≤|ω (.inl ())|} ∪
        ⋃ n : ℕ, {ω | ∃ k : Fin (2^n), B*(4/3:ℝ)^n ≤ |ω (.inr ⟨n,k⟩)|}) := measure_mono hsub
    _ ≤ law {ω | B≤|ω (.inl ())|} +
        ∑' n : ℕ, law {ω | ∃ k : Fin (2^n), B*(4/3:ℝ)^n ≤ |ω (.inr ⟨n,k⟩)|} :=
      (measure_union_le _ _).trans (add_le_add_right (measure_iUnion_le _) _)
    _ ≤ (ENNReal.ofReal B)⁻¹^8*moment8 +
        ∑' n : ℕ, (ENNReal.ofReal B)⁻¹^8*((2:ℝ≥0∞)*(4/3)⁻¹^8)^n*moment8 := by
      exact add_le_add (coordinate_tail8 _ hB) (ENNReal.tsum_le_tsum fun n ↦ scaled_badLevel_bound n hB)
    _ = _ := by
      rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_left,ENNReal.tsum_geometric]
      ring

lemma norm_wiener_tail_constant_finite :
    (1+(1-(2:ℝ≥0∞)*(4/3)⁻¹^8)⁻¹)*moment8 ≠ ∞ := by
  apply ENNReal.mul_ne_top _ moment8_ne_top
  apply ENNReal.add_ne_top.mpr
  refine ⟨by simp,?_⟩
  rw [ENNReal.inv_ne_top]
  apply ne_of_gt
  apply tsub_pos_of_lt
  have he : (2:ℝ≥0∞)*(4/3)⁻¹^8 = ENNReal.ofReal ((2:ℝ)*(4/3)⁻¹^8) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
      ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<4/3),
      ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3)]
    norm_num
  rw [he,ENNReal.ofReal_lt_one]
  norm_num

end HardSphere.Wiener

end

end OAI
