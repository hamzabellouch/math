import OAI.Analysis.CircleDomains.Sobolev.LipschitzArclengthBounds
import Mathlib.Analysis.Normed.Affine.AddTorsor

namespace OAI

/-! Concrete paths obtained by traversing a real interval in a Lipschitz chart. -/

open Set Function Metric
open scoped NNReal ENNReal

noncomputable section

namespace CircleDomainRigidity

def realIntervalPath (a b : ℝ) : C(PathTime, ℝ) where
  toFun s := AffineMap.lineMap a b (s : ℝ)
  continuous_toFun := (lipschitzWith_lineMap a b).continuous.comp continuous_subtype_val

@[simp] theorem realIntervalPath_zero (a b : ℝ) : realIntervalPath a b ⊥ = a := by
  simp [realIntervalPath]

@[simp] theorem realIntervalPath_one (a b : ℝ) : realIntervalPath a b ⊤ = b := by
  simp [realIntervalPath]

theorem realIntervalPath_lipschitz (a b : ℝ) :
    LipschitzWith (nndist a b) (realIntervalPath a b) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change dist (AffineMap.lineMap a b (s : ℝ)) (AffineMap.lineMap a b (t : ℝ)) ≤ _
  rw [dist_lineMap_lineMap, Subtype.dist_eq, coe_nndist, mul_comm]

theorem realIntervalPath_antilipschitz {a b : ℝ} (hab : a ≠ b) :
    AntilipschitzWith (nndist a b)⁻¹ (realIntervalPath a b) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro s t
  change dist s t ≤ _ * dist (AffineMap.lineMap a b (s : ℝ))
    (AffineMap.lineMap a b (t : ℝ))
  rw [dist_lineMap_lineMap, Subtype.dist_eq, NNReal.coe_inv, coe_nndist,
    mul_left_comm, inv_mul_cancel₀ (dist_ne_zero.mpr hab), mul_one]

theorem realIntervalPath_mem {a b : ℝ} (hab : a ≤ b) (s : PathTime) :
    realIntervalPath a b s ∈ Icc a b := by
  change AffineMap.lineMap a b (s : ℝ) ∈ Icc a b
  rw [AffineMap.lineMap_apply_module]
  simp only [smul_eq_mul]
  constructor <;> nlinarith [s.property.1, s.property.2]

theorem range_realIntervalPath {a b : ℝ} (hab : a < b) :
    range (realIntervalPath a b) = Icc a b := by
  apply Subset.antisymm
  · rintro _ ⟨s, rfl⟩
    exact realIntervalPath_mem hab.le s
  · intro y hy
    have hd : 0 < b - a := sub_pos.mpr hab
    let s : PathTime := ⟨(y-a)/(b-a), div_nonneg (sub_nonneg.mpr hy.1) hd.le,
      (div_le_one hd).mpr (sub_le_sub_right hy.2 a)⟩
    refine ⟨s, ?_⟩
    change AffineMap.lineMap a b ((y-a)/(b-a)) = y
    rw [AffineMap.lineMap_apply_module]
    dsimp
    field_simp
    ring

theorem lipschitz_path_boundedVariation {X : Type*} [MetricSpace X]
    {γ : PathTime → X} {L : ℝ≥0} (hL : LipschitzWith L γ) :
    BoundedVariationOn γ univ := by
  have hid : BoundedVariationOn (id : PathTime → PathTime) univ := by
    change eVariationOn (id : PathTime → PathTime) univ ≠ ∞
    rw [← Icc_bot_top, variation_time_identity (bot_le : (⊥ : PathTime) ≤ ⊤)]
    exact edist_ne_top _ _
  exact hL.comp_boundedVariationOn hid

variable {X : Type*} [MetricSpace X]

theorem intervalChart_lipschitz (φ : ℝ → X) {a b : ℝ} (hab : a ≤ b) {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) :
    LipschitzWith (L * nndist a b) (φ ∘ realIntervalPath a b) := by
    intro s t
    calc
      edist (φ (realIntervalPath a b s)) (φ (realIntervalPath a b t)) ≤
          L * edist (realIntervalPath a b s) (realIntervalPath a b t) :=
        hL (realIntervalPath_mem hab s) (realIntervalPath_mem hab t)
      _ ≤ (L * nndist a b : ℝ≥0) * edist s t := by
        calc
          _ ≤ (L : ℝ≥0∞) * ((nndist a b : ℝ≥0∞) * edist s t) :=
            mul_le_mul' le_rfl (realIntervalPath_lipschitz a b s t)
          _ = _ := by simp only [ENNReal.coe_mul, mul_assoc]

def intervalChartPath (φ : ℝ → X) {a b : ℝ} (hab : a ≤ b) {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) : RectifiablePath X :=
  let hl := intervalChart_lipschitz φ hab hL
  ⟨⟨φ ∘ realIntervalPath a b, hl.continuous⟩, lipschitz_path_boundedVariation hl⟩

theorem intervalChartPath_lipschitz (φ : ℝ → X) {a b : ℝ} (hab : a ≤ b) {L : ℝ≥0}
    (hL : LipschitzOnWith L φ (Icc a b)) :
    LipschitzWith (L * nndist a b) (intervalChartPath φ hab hL).val := by
  exact intervalChart_lipschitz φ hab hL

end CircleDomainRigidity

end

end OAI
