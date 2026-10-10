import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI


noncomputable section
namespace Pureness.CStarAlgebraNorm
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]

local instance (priority := 2000) completionFastNonAssoc (p : CStarAlgebraNorm R) :
    NonUnitalNonAssocSemiring p.Completion :=
  (completionCStarAlgebra p).toNonUnitalNonAssocSemiring
local instance (priority := 2000) completionFastAddMonoid (p : CStarAlgebraNorm R) :
    AddMonoid p.Completion :=
  (completionCStarAlgebra p).toAddMonoid
local instance (priority := 2000) completionFastNorm (p : CStarAlgebraNorm R) : Norm p.Completion :=
  (completionCStarAlgebra p).toNorm

def completionMap (p : CStarAlgebraNorm R) :
    letI := p.normedRing
    letI := p.normedAlgebra
    letI := p.cstarRing
    R →⋆ₙₐ[ℂ] p.Completion := by
  letI := p.normedRing
  letI := p.normedAlgebra
  letI := p.cstarRing
  exact
    { toFun := fun x => (x : UniformSpace.Completion R)
      map_zero' := UniformSpace.Completion.coe_zero
      map_add' := UniformSpace.Completion.coe_add
      map_smul' := UniformSpace.Completion.coe_smul
      map_mul' := Pureness.completion_coe_mul R
      map_star' := Pureness.completion_coe_star R }

lemma completionMap_norm (p : CStarAlgebraNorm R) (x : R) :
    ‖p.completionMap x‖ = p.toAlgebraNorm x := by
  let := p.normedRing
  let := p.normedAlgebra
  let := p.cstarRing
  exact UniformSpace.Completion.norm_coe x

lemma completionMap_injective (p : CStarAlgebraNorm R) : Function.Injective p.completionMap := by
  let := p.normedRing
  let := p.normedAlgebra
  let := p.cstarRing
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  apply eq_zero_of_map_eq_zero p.toAlgebraNorm
  change p.toAlgebraNorm x = 0
  rw [← completionMap_norm, hx, norm_zero]

theorem eq_original {A : Type*} [CStarAlgebra A] (p : CStarAlgebraNorm A) (a : A) :
    p.toAlgebraNorm a = ‖a‖ := by
  rw [← completionMap_norm]
  exact NonUnitalStarAlgHom.norm_map p.completionMap p.completionMap_injective a

end Pureness.CStarAlgebraNorm



namespace Pureness.CStarAlgebraNorm
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]

theorem le_of_bound (p q : CStarAlgebraNorm R) (C : ℝ)
    (h : ∀ x, p.toAlgebraNorm x ≤ C * q.toAlgebraNorm x) (x : R) :
    p.toAlgebraNorm x ≤ q.toAlgebraNorm x := by
  by_cases hx : x = 0
  · subst x
    simp
  have hqx : 0 < q.toAlgebraNorm x := map_pos_of_ne_zero q.toAlgebraNorm hx
  have hpowers (k : ℕ) : ∃ z : R,
      p.toAlgebraNorm z = p.toAlgebraNorm x ^ (2^k) ∧
      q.toAlgebraNorm z = q.toAlgebraNorm x ^ (2^k) := by
    induction k with
    | zero => exact ⟨x, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨z, hpz, hqz⟩ := ih
      refine ⟨star z*z, ?_, ?_⟩
      · rw [p.cstar, hpz, pow_succ, pow_mul, pow_two]
      · rw [q.cstar, hqz, pow_succ, pow_mul, pow_two]
  by_contra hle
  have hr : 1 < p.toAlgebraNorm x / q.toAlgebraNorm x :=
    (one_lt_div hqx).mpr (lt_of_not_ge hle)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hr
  obtain ⟨z, hpz, hqz⟩ := hpowers k
  have hb := h z
  rw [hpz, hqz] at hb
  have hb' : (p.toAlgebraNorm x / q.toAlgebraNorm x) ^ (2^k) ≤ C := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos hqx _)).mpr hb
  exact (not_lt_of_ge ((pow_le_pow_right₀ hr.le (Nat.le_of_lt (Nat.lt_two_pow_self))).trans hb')) hk

theorem eq_of_mutual_bound (p q : CStarAlgebraNorm R)
    (hpq : ∃ C : ℝ, ∀ x, p.toAlgebraNorm x ≤ C*q.toAlgebraNorm x)
    (hqp : ∃ C : ℝ, ∀ x, q.toAlgebraNorm x ≤ C*p.toAlgebraNorm x) : p=q := by
  obtain ⟨C, hC⟩ := hpq
  obtain ⟨D, hD⟩ := hqp
  have he : p.toAlgebraNorm=q.toAlgebraNorm := AlgebraNorm.ext (fun x =>
    le_antisymm (le_of_bound p q C hC x) (le_of_bound q p D hD x))
  cases p
  cases q
  cases he
  rfl

end Pureness.CStarAlgebraNorm

end

end OAI
