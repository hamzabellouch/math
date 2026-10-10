import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Traces.TraceAlgebra

namespace OAI

section

namespace UnitalTomsWinter

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nonempty (TracialState A)]

noncomputable def uniformTwoNorm (a : A) : ℝ :=
  sSup (Set.range fun τ : TracialState A => τ.twoNorm a)

omit [Nonempty (TracialState A)] in
lemma twoNorm_range_bddAbove (a : A) :
    BddAbove (Set.range fun τ : TracialState A => τ.twoNorm a) := by
  refine ⟨‖a‖, ?_⟩
  rintro _ ⟨τ, rfl⟩
  exact τ.twoNorm_le_norm a

omit [Nonempty (TracialState A)] in
theorem twoNorm_le_uniform (τ : TracialState A) (a : A) :
    τ.twoNorm a ≤ uniformTwoNorm a := le_csSup (twoNorm_range_bddAbove a) ⟨τ, rfl⟩

theorem uniformTwoNorm_nonneg (a : A) : 0 ≤ uniformTwoNorm a := by
  let τ : TracialState A := Classical.choice inferInstance
  exact (τ.twoNorm_nonneg a).trans (twoNorm_le_uniform τ a)

theorem uniformTwoNorm_le_norm (a : A) : uniformTwoNorm a ≤ ‖a‖ := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨τ, rfl⟩
  exact τ.twoNorm_le_norm a

@[simp] theorem uniformTwoNorm_zero : uniformTwoNorm (0 : A) = 0 := by
  apply le_antisymm _ (uniformTwoNorm_nonneg _)
  simpa using uniformTwoNorm_le_norm (0 : A)

@[simp] theorem uniformTwoNorm_one : uniformTwoNorm (1 : A) = 1 := by
  simp [uniformTwoNorm]

theorem uniformTwoNorm_add_le (a b : A) :
    uniformTwoNorm (a + b) ≤ uniformTwoNorm a + uniformTwoNorm b := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨τ, rfl⟩
  exact (τ.twoNorm_add_le a b).trans
    (add_le_add (twoNorm_le_uniform τ a) (twoNorm_le_uniform τ b))

omit [Nonempty (TracialState A)] in
@[simp] theorem uniformTwoNorm_star (a : A) :
    uniformTwoNorm (star a) = uniformTwoNorm a := by
  simp only [uniformTwoNorm, TracialState.twoNorm_star]

omit [Nonempty (TracialState A)] in
@[simp] theorem uniformTwoNorm_neg (a : A) :
    uniformTwoNorm (-a) = uniformTwoNorm a := by
  have ht (τ : TracialState A) : τ.twoNorm (-a) = τ.twoNorm a := by
    simp [TracialState.twoNorm]
  simp only [uniformTwoNorm, ht]

theorem uniformTwoNorm_smul_le (z : ℂ) (a : A) :
    uniformTwoNorm (z • a) ≤ ‖z‖ * uniformTwoNorm a := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨τ, rfl⟩
  exact (τ.twoNorm_smul z a).le.trans
    (mul_le_mul_of_nonneg_left (twoNorm_le_uniform τ a) (norm_nonneg z))

theorem uniformTwoNorm_mul_left (a b : A) :
    uniformTwoNorm (a * b) ≤ ‖a‖ * uniformTwoNorm b := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨τ, rfl⟩
  exact (τ.twoNorm_mul_left a b).trans
    (mul_le_mul_of_nonneg_left (twoNorm_le_uniform τ b) (norm_nonneg a))

theorem uniformTwoNorm_mul_right (a b : A) :
    uniformTwoNorm (b * a) ≤ ‖a‖ * uniformTwoNorm b := by
  rw [← uniformTwoNorm_star (b * a), star_mul]
  exact (uniformTwoNorm_mul_left (star a) (star b)).trans_eq (by simp)

theorem uniformTwoNorm_sub_le (a b : A) :
    |uniformTwoNorm a - uniformTwoNorm b| ≤ ‖a - b‖ := by
  have h₁ := (uniformTwoNorm_add_le (a - b) b).trans
    (add_le_add_left (uniformTwoNorm_le_norm (a - b)) (uniformTwoNorm b))
  have h₂ := (uniformTwoNorm_add_le (b - a) a).trans
    (add_le_add_left (uniformTwoNorm_le_norm (b - a)) (uniformTwoNorm a))
  simp only [sub_add_cancel, norm_sub_rev b a] at h₁ h₂
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem uniformTwoNorm_lipschitz : LipschitzWith 1 (uniformTwoNorm (A := A)) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
    uniformTwoNorm_sub_le a b

theorem continuous_uniformTwoNorm : Continuous (uniformTwoNorm (A := A)) :=
  uniformTwoNorm_lipschitz.continuous

end UnitalTomsWinter

end

end OAI
