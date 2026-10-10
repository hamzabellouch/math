import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientNorm

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexStarModule
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (T : CuntzPureness.PositiveQuasitrace D)

lemma selfAdjointValue_sub_abs_le (a b : selfAdjoint D) :
    |T.selfAdjointValue a-T.selfAdjointValue b| ≤ ‖a.1-b.1‖*T ⟨1,zero_le_one⟩ := by
  let C := max ‖a.1‖ ‖b.1‖
  have hC : 0 ≤ C := le_max_of_le_left (norm_nonneg _)
  have ha : ‖a.1‖ ≤ C := le_max_left _ _
  have hb : ‖b.1‖ ≤ C := le_max_right _ _
  let p : Positive D := ⟨a.1+C • 1,selfAdjoint_add_bound_nonneg a C ha⟩
  let q : Positive D := ⟨b.1+C • 1,selfAdjoint_add_bound_nonneg b C hb⟩
  have h1 := T.le_add_norm p q
  have h2 := T.le_add_norm q p
  have hdiff : p.1-q.1 = a.1-b.1 := by dsimp [p,q]; abel
  rw [norm_sub_rev q.1 p.1,hdiff] at h2
  rw [hdiff] at h1
  rw [T.selfAdjointValue_shift a C hC ha,T.selfAdjointValue_shift b C hC hb,abs_sub_le_iff]
  change T p-C*T ⟨1,zero_le_one⟩-(T q-C*T ⟨1,zero_le_one⟩) ≤ _ ∧ _
  constructor <;> linarith

lemma complexValue_sub_norm_le (x y : D) :
    ‖T.complexValue x-T.complexValue y‖ ≤ (2*T ⟨1,zero_le_one⟩)*‖x-y‖ := by
  have hT := T.nonneg (⟨1,zero_le_one⟩ : Positive D)
  have hr := T.selfAdjointValue_sub_abs_le (ℜ x) (ℜ y)
  have hi := T.selfAdjointValue_sub_abs_le (ℑ x) (ℑ y)
  have hrn : ‖(ℜ x).1-(ℜ y).1‖ ≤ ‖x-y‖ := by
    have h := realPart.norm_le (x-y)
    rw [map_sub] at h
    exact h
  have hin : ‖(ℑ x).1-(ℑ y).1‖ ≤ ‖x-y‖ := by
    have h := imaginaryPart.norm_le (x-y)
    rw [map_sub] at h
    exact h
  have he : T.complexValue x-T.complexValue y =
      ((T.selfAdjointValue (ℜ x)-T.selfAdjointValue (ℜ y) : ℝ) : ℂ)+
      Complex.I*((T.selfAdjointValue (ℑ x)-T.selfAdjointValue (ℑ y) : ℝ) : ℂ) := by
    simp only [complexValue,Complex.ofReal_sub]; ring
  rw [he]
  calc
    _ ≤ ‖((T.selfAdjointValue (ℜ x)-T.selfAdjointValue (ℜ y) : ℝ) : ℂ)‖+
        ‖Complex.I*((T.selfAdjointValue (ℑ x)-T.selfAdjointValue (ℑ y) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = |T.selfAdjointValue (ℜ x)-T.selfAdjointValue (ℜ y)|+
        |T.selfAdjointValue (ℑ x)-T.selfAdjointValue (ℑ y)| := by rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
    _ ≤ ‖(ℜ x).1-(ℜ y).1‖*T ⟨1,zero_le_one⟩+‖(ℑ x).1-(ℑ y).1‖*T ⟨1,zero_le_one⟩ := add_le_add hr hi
    _ ≤ ‖x-y‖*T ⟨1,zero_le_one⟩+‖x-y‖*T ⟨1,zero_le_one⟩ :=
      add_le_add (mul_le_mul_of_nonneg_right hrn hT) (mul_le_mul_of_nonneg_right hin hT)
    _ = _ := by ring

lemma complexValue_lipschitz : LipschitzWith ⟨2*T ⟨1,zero_le_one⟩,mul_nonneg (by norm_num) (T.nonneg _)⟩ T.complexValue := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  exact T.complexValue_sub_norm_le x y
end CuntzPureness.PositiveQuasitrace

end

end OAI
