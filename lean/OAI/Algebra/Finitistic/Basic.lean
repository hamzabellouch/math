import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.Finiteness.Defs

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]

/-- The little finitistic dimension: the supremum of the actual projective
dimensions of finitely generated modules whose projective dimension is finite.
The value of the zero module follows mathlib's -∞ convention. -/
def littleFinitisticDimension : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{u} A) (_ : Module.Finite A M) (_ : projectiveDimension M < ⊤),
    projectiveDimension M

theorem le_littleFinitisticDimension (M : ModuleCat.{u} A) [Module.Finite A M]
    (h : projectiveDimension M < ⊤) :
    projectiveDimension M ≤ littleFinitisticDimension A := by
  unfold littleFinitisticDimension
  exact le_iSup_of_le M (le_iSup_of_le inferInstance (le_iSup_of_le h le_rfl))

/-- Unbounded finite projective dimensions of actual finitely generated modules
force the little finitistic dimension to be infinite. -/
theorem littleFinitisticDimension_eq_top_of_unbounded
    (h : ∀ n : ℕ, ∃ M : ModuleCat.{u} A, Module.Finite A M ∧
      projectiveDimension M < ⊤ ∧ (n : WithBot ℕ∞) ≤ projectiveDimension M) :
    littleFinitisticDimension A = ⊤ := by
  apply ENat.WithBot.eq_top_iff_forall_ge.mpr
  intro n
  obtain ⟨M, hM, hfinite, hn⟩ := h n
  let := hM
  exact hn.trans (le_littleFinitisticDimension A M hfinite)

/-- The manuscript's concrete lower-bound pattern is sufficient; all finite
projective-dimension premises must still be supplied by the constructed modules. -/
theorem littleFinitisticDimension_eq_top_of_two_mul_bounds
    (h : ∀ m : ℕ, 0 < m → ∃ M : ModuleCat.{u} A, Module.Finite A M ∧
      projectiveDimension M < ⊤ ∧ ((2*m-2 : ℕ) : WithBot ℕ∞) ≤ projectiveDimension M) :
    littleFinitisticDimension A = ⊤ := by
  apply littleFinitisticDimension_eq_top_of_unbounded
  intro n
  obtain ⟨M,hM,hfinite,hm⟩ := h (n+1) (by omega)
  refine ⟨M,hM,hfinite,le_trans ?_ hm⟩
  exact_mod_cast (show n ≤ 2*(n+1)-2 by omega)
end LittleFinitistic

end

end OAI
