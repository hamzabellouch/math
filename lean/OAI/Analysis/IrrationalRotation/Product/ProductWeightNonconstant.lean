import OAI.Analysis.IrrationalRotation.Product.ProductOrbitFiberNull
import OAI.Analysis.IrrationalRotation.Spectral.ProductPolarDiffuse

namespace OAI

open MeasureTheory Set Filter
open scoped ENNReal

namespace Invariant233.ProductModel

theorem logarithmicCost_coordinate_increase
    (θ c : ℕ → ℝ) (j : ℕ) (x y : Base)
    (hxy : ∀ i, i ≠ j → y i = x i)
    (hx : ⌊circleRepresentative (x j) + θ j⌋ = (0 : ℤ))
    (hy : ⌊circleRepresentative (y j) + θ j⌋ = (1 : ℤ)) :
    logarithmicCost θ c y = ENNReal.ofReal (c j) + logarithmicCost θ c x := by
  unfold logarithmicCost
  rw [ENNReal.tsum_eq_add_tsum_ite j]
  conv_rhs => arg 2; rw [ENNReal.tsum_eq_add_tsum_ite j]
  simp only [hx, hy, Int.cast_zero, Int.cast_one, mul_zero, mul_one,
    ENNReal.ofReal_zero, zero_add]
  congr 1
  apply tsum_congr
  intro i
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, hxy i hij]

theorem measure_representative_cylinder (j : ℕ) {a : ℝ} (ha : a ≤ 1) :
    baseMeasure {x | circleRepresentative (x j) ∈ Ico (0 : ℝ) a} =
      ENNReal.ofReal a := by
  have hmp : MeasurePreserving
      (fun x : Base => circleRepresentative (x j)) baseMeasure
      (volume.restrict (Ico (0 : ℝ) 1)) :=
    CocycleSupport.measurePreserving_productRepresentative j
  change baseMeasure ((fun x : Base => circleRepresentative (x j)) ⁻¹' Ico (0 : ℝ) a) = _
  rw [← Measure.map_apply hmp.measurable measurableSet_Ico, hmp.map_eq,
    Measure.restrict_apply measurableSet_Ico,
    inter_eq_left.mpr (Ico_subset_Ico le_rfl ha), Real.volume_Ico, sub_zero]

theorem weight_not_ae_constant_of_ae_ne_zero
    (θ c : ℕ → ℝ) (j : ℕ) (hθj : 0 < θ j ∧ θ j < 1) (hcj : 0 < c j)
    (hne : ∀ᵐ x ∂baseMeasure, weight θ c x ≠ 0) :
    ¬ ∃ a : ℝ, weight θ c =ᵐ[baseMeasure] Function.const Base a := by
  rintro ⟨a, ha⟩
  let α : ℕ → ℝ := fun i => if i = j then 1 - θ j else 0
  let σ : Base → Base := rotation α
  have hmp : MeasurePreserving σ baseMeasure baseMeasure := measurePreserving_rotation α
  let d : ℝ := min (θ j) (1 - θ j)
  have hdpos : 0 < d := lt_min hθj.1 (by linarith [hθj.2])
  have hdθ : d ≤ θ j := min_le_left _ _
  have hdθ' : d ≤ 1 - θ j := min_le_right _ _
  have hd1 : d ≤ 1 := le_trans hdθ hθj.2.le
  have hs : baseMeasure {x | circleRepresentative (x j) ∈ Ico (0 : ℝ) d} ≠ 0 := by
    rw [measure_representative_cylinder j hd1]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hdpos)
  have hall : ∀ᵐ x ∂baseMeasure,
      weight θ c x = a ∧ weight θ c (σ x) = a ∧ weight θ c x ≠ 0 := by
    filter_upwards [ha, hmp.quasiMeasurePreserving.ae ha, hne] with x hx hy hn
    exact ⟨hx, hy, hn⟩
  obtain ⟨x, hx, hxvalue, hyvalue, hxne⟩ :=
    ((frequently_ae_iff.mpr hs).and_eventually hall).exists
  have hj : σ x j = x j + ((1 - θ j : ℝ) : Circle) := by simp [σ, rotation, α]
  have hother (i : ℕ) (hij : i ≠ j) : σ x i = x i := by
    simp [σ, rotation, α, hij]
  have hrep : circleRepresentative (σ x j) = circleRepresentative (x j) + (1 - θ j) := by
    rw [hj]
    change ProductCocycle.representative (x j + ((1 - θ j : ℝ) : Circle)) = _
    rw [ProductCocycle.representative_add]
    apply Int.fract_eq_self.mpr
    change 0 ≤ circleRepresentative (x j) + (1 - θ j) ∧
      circleRepresentative (x j) + (1 - θ j) < 1
    constructor <;> linarith [hx.1, hx.2]
  have hfloorx : ⌊circleRepresentative (x j) + θ j⌋ = (0 : ℤ) := by
    apply Int.floor_eq_zero_iff.mpr
    constructor <;> linarith [hx.1, hx.2]
  have hfloory : ⌊circleRepresentative (σ x j) + θ j⌋ = (1 : ℤ) := by
    rw [hrep]
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith [hx.1, hx.2]
  have hincrease := logarithmicCost_coordinate_increase θ c j x (σ x) hother hfloorx hfloory
  have hequal : logarithmicCost θ c (σ x) = logarithmicCost θ c x := by
    rw [← negLogCost_weight, ← negLogCost_weight, hxvalue, hyvalue]
  have hfinite : logarithmicCost θ c x ≠ ∞ := fun h =>
    hxne ((weight_eq_zero_iff θ c x).mpr h)
  have hlt := ENNReal.lt_add_right hfinite (ne_of_gt (ENNReal.ofReal_pos.mpr hcj))
  rw [add_comm, ← hincrease, hequal] at hlt
  exact (lt_irrefl _) hlt

theorem weight_not_ae_constant (θ c : ℕ → ℝ)
    (hadm : AdmissibleAnglesAndCosts θ c) :
    ¬ ∃ a : ℝ, weight θ c =ᵐ[baseMeasure] Function.const Base a := by
  apply weight_not_ae_constant_of_ae_ne_zero θ c 0
    ⟨(hadm.1 0).1, (hadm.1 0).2.1⟩ (hadm.1 0).2.2
  exact (ae_weight_pos θ c (fun i => (hadm.1 i).1.le)
    (fun i => (hadm.1 i).2.2.le) hadm.2.1).mono (fun _ hx => hx.ne')

theorem weight_rotation_joint_fiber_measure_zero_of_admissible
    (θ c : ℕ → ℝ) (hadm : AdmissibleAnglesAndCosts θ c) (z : ℤ → ℝ) :
    baseMeasure {x | ∀ n : ℤ, weight θ c (rotationIterate θ n x) = z n} = 0 :=
  rotation_joint_fiber_measure_zero hadm.2.2 (measurable_weight θ c)
    (weight_not_ae_constant θ c hadm) z

theorem fullPolarAlgebra_weight_diffuse_of_admissible
    (θ c : ℕ → ℝ) (hadm : AdmissibleAnglesAndCosts θ c) :
    IsDiffuseVonNeumannAlgebra
      (fullPolarAlgebra shiftOperator (star shiftOperator * weightedOperator θ c)) := by
  rw [star_shift_weightedOperator_eq_multiplier]
  obtain ⟨S, hS, -, hmem⟩ := ae_weight_mem_countable θ c
    (fun i => ⟨(hadm.1 i).1.le, (hadm.1 i).2.1⟩)
    (fun i => (hadm.1 i).2.2.le) hadm.2.1
  exact fullPolarAlgebra_multiplier_diffuse_of_null_fibers θ (weight θ c) 1
    (by norm_num) (measurable_weight θ c) (weight_complex_norm_le_one θ c)
    ⟨S, hS, hmem⟩ (weight_rotation_joint_fiber_measure_zero_of_admissible θ c hadm)

end Invariant233.ProductModel

end OAI
