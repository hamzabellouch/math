import OAI.MeasureTheory.Falconer.Radial.RadialTestFatou
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Uniform finite-energy control of the actual radial test norms. -/
namespace Falconer
open Set MeasureTheory Filter PlanarFalconer
open scoped ENNReal NNReal Topology

theorem euclidean_radial_testNorm_moment_bound (n : ℕ)
    (α β : Measure (Space (n+1))) [IsFiniteMeasure α] [IsFiniteMeasure β]
    [NullSingletonClass α] {K : Set (Space (n+1))} (hK : IsCompact K)
    (hα : ∀ᵐ z ∂α, z ∈ K) {s t p q D : ℝ}
    (hs0 : 0 < s) (hs : (n : ℝ) < s) (hsn : s < n+1) (hs2 : s < 2*n)
    (ht : 0 < t) (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (hupt : (2*n-s)*p < t) (htr : t/(2-p) < n) (hD : 0 < D)
    (hdiam : ∀ᵐ z : Space (n+1) × Space (n+1) ∂β.prod β, dist z.1 z.2 ≤ D)
    (hbound : ∀ᵐ x ∂β, ∀ y ∈ K, dist y x ≤ D) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      (∫⁻ x, (surfaceTestNorm q (α.map (radialDirection x)))^p ∂β) ≤
        C * (rieszEnergyOn β t)^(1/2 : ℝ) * (rieszEnergyOn α s)^(p/2) := by
  obtain ⟨C,hC,h⟩ := mollified_euclidean_radial_moment_bound n α β hK hα
    hs0 hs hsn hs2 ht hpq hp2 hupt htr hD hdiam hbound
  let ε := fun k : ℕ => 1/((k : ℝ)+1)
  have hε (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hε1 (k : ℕ) : ε k ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨C,hC,(euclidean_radial_testNorm_fatou α β hε hlim hpq).trans ?_⟩
  have hl := liminf_le_liminf (f := atTop)
    (Eventually.of_forall (fun k => h (ε k) (hε k) (hε1 k)))
  simpa only [liminf_const] using hl

theorem finite_euclidean_radial_testNorm_moment (n : ℕ)
    (α β : Measure (Space (n+1))) [IsFiniteMeasure α] [IsFiniteMeasure β]
    {K L : Set (Space (n+1))} (hK : IsCompact K) (hL : IsCompact L)
    (hα : ∀ᵐ z ∂α, z ∈ K) (hβ : ∀ᵐ z ∂β, z ∈ L) {s t p q : ℝ}
    (hs0 : 0 < s) (hs : (n : ℝ) < s) (hsn : s < n+1) (hs2 : s < 2*n)
    (ht : 0 < t) (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (hupt : (2*n-s)*p < t) (htr : t/(2-p) < n)
    (hEα : rieszEnergyOn α s < ∞) (hEβ : rieszEnergyOn β t < ∞) :
    (∫⁻ x, (surfaceTestNorm q (α.map (radialDirection x)))^p ∂β) < ∞ := by
  let := nullSingletonClass_of_finite_rieszEnergy α hs0 hEα
  let D := Metric.diam (K ∪ L) + 1
  have hD : 0 < D := add_pos_of_nonneg_of_pos Metric.diam_nonneg zero_lt_one
  have hdist {x y : Space (n+1)} (hx : x ∈ K ∪ L) (hy : y ∈ K ∪ L) : dist x y ≤ D :=
    (Metric.dist_le_diam_of_mem (hK.union hL).isBounded hx hy).trans
      (le_add_of_nonneg_right zero_le_one)
  have hbound : ∀ᵐ x ∂β, ∀ y ∈ K, dist y x ≤ D :=
    hβ.mono (fun x hx y hy => hdist (Or.inl hy) (Or.inr hx))
  have hdiam : ∀ᵐ z : Space (n+1) × Space (n+1) ∂β.prod β, dist z.1 z.2 ≤ D := by
    apply (Measure.ae_prod_iff_ae_ae
      ((isClosed_le (continuous_fst.dist continuous_snd) continuous_const).measurableSet)).mpr
    filter_upwards [hβ] with x hx
    filter_upwards [hβ] with y hy
    exact hdist (Or.inr hx) (Or.inr hy)
  obtain ⟨C,hC,hb⟩ := euclidean_radial_testNorm_moment_bound n α β hK hα hs0 hs hsn hs2
    ht hpq hp2 hupt htr hD hdiam hbound
  exact hb.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hEβ.ne).lt_top)
    (ENNReal.rpow_ne_top_of_nonneg (by linarith [hpq.pos]) hEα.ne).lt_top)

end Falconer

end OAI
