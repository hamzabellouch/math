import OAI.Analysis.Pureness.Quasitrace.QuasitraceFamily

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace
open scoped NNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (T : PositiveQuasitrace D)

lemma le_add_norm (a b : Positive D) :
    T a ≤ T b+‖a.1-b.1‖*T ⟨1,zero_le_one⟩ := by
  have hab : a ≤ Positive.add b (Positive.smul ‖a.1-b.1‖₊ ⟨1,zero_le_one⟩) := by
    change a.1 ≤ b.1+‖a.1-b.1‖ • (1 : D)
    have h := (a.2.isSelfAdjoint.sub b.2.isSelfAdjoint).le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one,sub_le_iff_le_add] at h
    simpa only [add_comm] using h
  have hcomm : Commute b.1 (Positive.smul ‖a.1-b.1‖₊ (⟨1,zero_le_one⟩ : Positive D)).1 :=
    (Commute.one_right _).smul_right ‖a.1-b.1‖
  have h := T.monotone hab
  rw [T.map_add_commute _ _ hcomm,T.map_smul] at h
  exact h

theorem lipschitz : LipschitzWith ⟨T ⟨1,zero_le_one⟩,T.nonneg _⟩ T := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [Real.dist_eq,abs_sub_le_iff]
  have h1 := T.le_add_norm a b
  have h2 := T.le_add_norm b a
  simp only [Subtype.dist_eq,dist_eq_norm]
  change T a-T b ≤ T ⟨1,zero_le_one⟩*‖a.1-b.1‖ ∧ T b-T a ≤ T ⟨1,zero_le_one⟩*‖a.1-b.1‖
  rw [norm_sub_rev b.1 a.1] at h2
  constructor <;> nlinarith

theorem continuous : Continuous T := T.lipschitz.continuous
end CuntzPureness.PositiveQuasitrace

end

end OAI
