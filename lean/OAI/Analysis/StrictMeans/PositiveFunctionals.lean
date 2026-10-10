import OAI.Analysis.StrictMeans.SpectralGrowth

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology

open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

lemma continuousMap_order_bound (f : C(X, ℝ)) :
    -(‖f‖ • (1 : C(X, ℝ))) ≤ f ∧ f ≤ ‖f‖ • (1 : C(X, ℝ)) := by
  constructor <;> intro x
  · have h := (abs_le.mp (f.norm_coe_le_norm x)).1
    simpa using h
  · have h := (abs_le.mp (f.norm_coe_le_norm x)).2
    simpa using h

omit [CompactSpace X] in
lemma positiveOperator_unit_nonneg (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hL : Monotone L) :
    0 ≤ L 1 := by
  simpa only [map_zero] using hL (show (0 : C(X, ℝ)) ≤ 1 by intro x; simp)

lemma positiveOperator_apply_abs_le (L : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hL : Monotone L) (f : C(X, ℝ)) (x : X) :
    |L f x| ≤ ‖f‖ * L 1 x := by
  have hlo := hL (continuousMap_order_bound f).1
  have hhi := hL (continuousMap_order_bound f).2
  rw [map_neg, map_smul] at hlo
  rw [map_smul] at hhi
  exact abs_le.mpr ⟨by simpa using hlo x, by simpa using hhi x⟩

lemma positiveOperator_norm [Nonempty X] (L : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hL : Monotone L) : ‖L‖ = ‖L 1‖ := by
  apply le_antisymm
  · apply L.opNorm_le_bound (norm_nonneg _)
    intro f
    apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    intro x
    rw [Real.norm_eq_abs]
    calc
      |L f x| ≤ ‖f‖ * L 1 x := positiveOperator_apply_abs_le L hL f x
      _ ≤ ‖f‖ * ‖L 1‖ := mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans ((L 1).norm_coe_le_norm x)) (norm_nonneg _)
      _ = _ := mul_comm _ _
  · simpa only [norm_one, mul_one] using L.le_opNorm (1 : C(X, ℝ))

lemma positiveOperator_pow_monotone (L : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hL : Monotone L) (n : ℕ) : Monotone (L ^ n) := by
  induction n with
  | zero => simpa using (monotone_id : Monotone (id : C(X, ℝ) → C(X, ℝ)))
  | succ n ih =>
    rw [pow_succ']
    intro f g h
    exact hL (ih h)

lemma positiveOperator_pow_norm [Nonempty X] (L : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hL : Monotone L) (n : ℕ) : ‖L ^ n‖ = ‖(L ^ n) 1‖ :=
  positiveOperator_norm (L ^ n) (positiveOperator_pow_monotone L hL n)

lemma positiveOperator_iterate_bound [Nonempty X]
    (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hL : Monotone L)
    (g : C(X, ℝ)) {a M : ℝ} (ha : 0 ≤ a)
    (hg : (1 : C(X, ℝ)) ≤ g) (hM : g ≤ M • (1 : C(X, ℝ)))
    (hsuper : L g ≤ a • g) (n : ℕ) : ‖L ^ n‖ ≤ M * a ^ n := by
  have hM0 : 0 ≤ M := by
    obtain ⟨x⟩ := ‹Nonempty X›
    have hh := (hg.trans hM) x
    have : (1 : ℝ) ≤ M := by simpa using hh
    linarith
  have hp : (L ^ n) g ≤ a ^ n • g := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      change L ((L ^ n) g) ≤ a ^ (n + 1) • g
      calc
        L ((L ^ n) g) ≤ L (a ^ n • g) := hL ih
        _ = a ^ n • L g := L.map_smul _ _
        _ ≤ a ^ n • (a • g) := smul_le_smul_of_nonneg_left hsuper (pow_nonneg ha n)
        _ = a ^ (n + 1) • g := by rw [smul_smul, pow_succ]
  rw [positiveOperator_pow_norm L hL n]
  apply (ContinuousMap.norm_le _ (mul_nonneg hM0 (pow_nonneg ha n))).mpr
  intro x
  have hn := positiveOperator_unit_nonneg (L ^ n) (positiveOperator_pow_monotone L hL n) x
  change (0 : ℝ) ≤ ((L ^ n) 1) x at hn
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  have h1 := positiveOperator_pow_monotone L hL n hg x
  have h2 := hp x
  have h3 := hM x
  change ((L ^ n) 1) x ≤ ((L ^ n) g) x at h1
  change ((L ^ n) g) x ≤ a ^ n * g x at h2
  change g x ≤ M * 1 at h3
  calc
    ((L ^ n) 1) x ≤ a ^ n * g x := h1.trans h2
    _ ≤ a ^ n * M := mul_le_mul_of_nonneg_left (by simpa using h3) (pow_nonneg ha n)
    _ = M * a ^ n := mul_comm _ _

def compactTestFunctional (Λ : C(X, ℝ) →L[ℝ] ℝ) (hΛ : Monotone Λ) :
    CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ where
  toFun f := Λ f.toContinuousMap
  map_add' f g := by exact Λ.map_add f.toContinuousMap g.toContinuousMap
  map_smul' c f := by exact Λ.map_smul c f.toContinuousMap
  monotone' := fun _ _ h => hΛ h

variable [T2Space X] [MeasurableSpace X] [BorelSpace X]

lemma exists_probabilityMeasure_of_positiveFunctional
    (Λ : C(X, ℝ) →L[ℝ] ℝ) (hΛ : Monotone Λ) (h1 : Λ 1 = 1) :
    ∃ μ : ProbabilityMeasure X, ∀ f : C(X, ℝ), ∫ x, f x ∂(μ : Measure X) = Λ f := by
  let Λc := compactTestFunctional Λ hΛ
  let μ := RealRMK.rieszMeasure Λc
  have he (f : C(X, ℝ)) : ∫ x, f x ∂μ = Λ f := by
    let fc : CompactlySupportedContinuousMap X ℝ :=
      { toContinuousMap := f
        hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
    exact RealRMK.integral_rieszMeasure Λc fc
  have hμ : IsProbabilityMeasure μ := by
    constructor
    apply (ENNReal.toReal_eq_one_iff _).mp
    change μ.real univ = 1
    have hh := he (1 : C(X, ℝ))
    simpa only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one, h1] using hh
  exact ⟨⟨μ, hμ⟩, he⟩

end
end StrictInverseFirstPower

end

end OAI
