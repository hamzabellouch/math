import OAI.Probability.InvariantIsing.Magnetic.MagneticBlockPath
import OAI.Probability.InvariantIsing.Magnetic.MagneticVariational

namespace OAI

/-! The weighted overlap path for the same field groups as the magnetic
variational functional. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal
namespace InvariantIsing

def magneticGroupLevel {A : Type*} [Fintype A] (γ mag : A → ℝ) (h : FieldStep)
    (i : Fin (h.depth+1)) : ℝ := ∑ a, γ a * magneticFieldLevel h (mag a) i

lemma magneticGroupLevel_mem_unit {A : Type*} [Fintype A]
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (h : FieldStep) (i : Fin (h.depth+1)) : magneticGroupLevel γ mag h i ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun a _ => mul_nonneg (hγ a) (magneticFieldLevel_mem_unit h (mag a) i).1
  · calc
      _ ≤ ∑ a, γ a * 1 := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (magneticFieldLevel_mem_unit h (mag a) i).2 (hγ a)
      _ = 1 := by simpa only [mul_one] using hγsum

lemma magneticGroupLevel_monotone {A : Type*} [Fintype A]
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (h : FieldStep) :
    Monotone (magneticGroupLevel γ mag h) := by
  intro i j hij
  exact Finset.sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_left (magneticFieldLevel_monotone h (mag a) hij) (hγ a)

def magneticGroupPath {A : Type*} [Fintype A] (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1) (h : FieldStep) : OverlapPath :=
  fieldLevelPath h (magneticGroupLevel γ mag h) (magneticGroupLevel_monotone γ mag hγ h)
    (magneticGroupLevel_mem_unit γ mag hγ hγsum h)

lemma magneticGroupPath_on_cell {A : Type*} [Fintype A] (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1) (h : FieldStep)
    (i : Fin (h.depth+1)) {s : ℝ} (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    magneticGroupPath γ mag hγ hγsum h s = magneticGroupLevel γ mag h i :=
  fieldLevelPath_on_cell h _ _ _ i hs

lemma magneticGroupPath_eq_sum {A : Type*} [Fintype A] (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1) (h : FieldStep) (s : ℝ) :
    magneticGroupPath γ mag hγ hγsum h s = ∑ a, γ a * magneticFieldPath h (mag a) s := by
  rfl

end InvariantIsing

end

end OAI
