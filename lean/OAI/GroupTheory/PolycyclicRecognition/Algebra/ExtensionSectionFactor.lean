import Mathlib.GroupTheory.GroupExtension.Basic

namespace OAI

/-! # The normalized factor system of an actual group extension -/

noncomputable section
namespace PolycyclicRecognition
variable {N G Q : Type*} [Group N] [Group G] [Group Q]
open Classical

/-- A normalized section exists for every surjective group extension. -/
def normalizedExtensionSection (S : GroupExtension N G Q) : S.Section where
  toFun q := if q = 1 then 1 else S.surjInvRightHom q
  rightInverse_rightHom q := by
    dsimp only
    split_ifs with h
    · simp only [h, map_one]
    · exact S.surjInvRightHom.rightInverse_rightHom q

@[simp] theorem normalizedExtensionSection_one (S : GroupExtension N G Q) :
    normalizedExtensionSection S 1 = 1 := by
  simp [normalizedExtensionSection]

namespace GroupExtensionSection
variable (S : GroupExtension N G Q) (σ : S.Section)

/-- This element measures the failure of the chosen section to multiply. -/
def factor (q r : Q) : N :=
  Classical.choose (σ.mul_mul_mul_inv_mem_range_inl q r)

@[simp] theorem inl_factor (q r : Q) :
    S.inl (factor S σ q r) = σ q * σ r * (σ (q * r))⁻¹ :=
  Classical.choose_spec (σ.mul_mul_mul_inv_mem_range_inl q r)

theorem section_mul (q r : Q) :
    σ q * σ r = S.inl (factor S σ q r) * σ (q * r) := by
  rw [inl_factor, inv_mul_cancel_right]

theorem factor_one_left (hσ : σ 1 = 1) (q : Q) : factor S σ 1 q = 1 := by
  apply S.inl_injective
  simp only [inl_factor, hσ, one_mul, mul_inv_cancel, map_one]

theorem factor_one_right (hσ : σ 1 = 1) (q : Q) : factor S σ q 1 = 1 := by
  apply S.inl_injective
  simp only [inl_factor, hσ, mul_one, mul_inv_cancel, map_one]

/-- The exact nonabelian two-cocycle identity. -/
theorem factor_cocycle (q r s : Q) :
    factor S σ q r * factor S σ (q * r) s =
      S.conjAct (σ q) (factor S σ r s) * factor S σ q (r * s) := by
  apply S.inl_injective
  simp only [map_mul, inl_factor, S.inl_conjAct_comm]
  rw [mul_assoc q r s]
  group

/-- Conjugation by the section multiplies up to the stated inner factor. -/
theorem section_action_mul (q r : Q) :
    S.conjAct (σ q) * S.conjAct (σ r) =
      MulAut.conj (factor S σ q r) * S.conjAct (σ (q * r)) := by
  apply DFunLike.ext
  intro x
  apply S.inl_injective
  change S.inl (S.conjAct (σ q) (S.conjAct (σ r) x)) =
    S.inl (factor S σ q r * S.conjAct (σ (q * r)) x * (factor S σ q r)⁻¹)
  simp only [S.inl_conjAct_comm, map_mul, map_inv, inl_factor]
  group

end GroupExtensionSection
end PolycyclicRecognition

end

end OAI
