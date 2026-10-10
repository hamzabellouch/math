import OAI.Analysis.Pureness.Divisibility.Fullness
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

namespace OAI
namespace CuntzPureness
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

structure TracialState (A : Type*) [CStarAlgebra A] [PartialOrder A] where
  functional : A →ₚ[ℂ] ℂ
  normalized : functional 1 = 1
  tracial : ∀ a b : A, functional (a * b) = functional (b * a)

namespace TracialState

theorem conjugate_le (τ : TracialState A) (h : A) (hh : 0 ≤ h) (s : A) :
    τ.functional (star s * h * s) ≤ ‖s * star s‖ • τ.functional h := by
  have hsqrt : star (CFC.sqrt h) = CFC.sqrt h := (CFC.sqrt_nonneg h).star_eq
  have hsquare (z : A) : CFC.sqrt h * (CFC.sqrt h * z) = h * z := by
    rw [← mul_assoc, CFC.sqrt_mul_sqrt_self h hh]
  have heq : τ.functional (star s * h * s) =
      τ.functional (CFC.sqrt h * (s * star s) * CFC.sqrt h) := by
    calc
      τ.functional (star s * h * s) =
          τ.functional ((star s * CFC.sqrt h) * (CFC.sqrt h * s)) := by
        simp only [mul_assoc, hsquare]
      _ = τ.functional ((CFC.sqrt h * s) * (star s * CFC.sqrt h)) := τ.tracial _ _
      _ = τ.functional (CFC.sqrt h * (s * star s) * CFC.sqrt h) := by simp only [mul_assoc]
  have hb : CFC.sqrt h * (s * star s) * CFC.sqrt h ≤ ‖s * star s‖ • h := by
    simpa only [hsqrt, CFC.sqrt_mul_sqrt_self h hh] using
      (CStarAlgebra.star_left_conjugate_le_norm_smul
        (a := CFC.sqrt h) (b := s * star s) (mul_star_self_nonneg s).isSelfAdjoint)
  rw [heq, ← τ.functional.map_smul_of_tower]
  exact τ.functional.monotone hb

theorem faithful (τ : TracialState A) (hsimple : TopologicallySimple A)
    (h : A) (hh : 0 ≤ h) (hzero : τ.functional h = 0) : h = 0 := by
  by_contra hne
  obtain ⟨n, s, hs⟩ := fullness hsimple h hh hne
  have hz (i : Fin n) : τ.functional (star (s i) * h * s i) = 0 := by
    apply le_antisymm
    · simpa only [hzero, smul_zero] using τ.conjugate_le h hh (s i)
    · exact τ.functional.map_nonneg (star_left_conjugate_nonneg hh (s i))
  have h1 : τ.functional 1 = 0 := by
    rw [← hs, map_sum]
    exact Finset.sum_eq_zero (fun i _ => hz i)
  exact one_ne_zero (τ.normalized.symm.trans h1)

theorem map_eq_zero_iff (τ : TracialState A) (hsimple : TopologicallySimple A)
    (h : A) (hh : 0 ≤ h) : τ.functional h = 0 ↔ h = 0 :=
  ⟨τ.faithful hsimple h hh, fun heq => by simp [heq]⟩
end TracialState
end CuntzPureness

end OAI
