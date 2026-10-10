import OAI.Analysis.Pureness.GroupAlgebra.WordRadialFeature

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped InnerProductSpace lp
local instance {X : Type*} : DecidableEq X := Classical.decEq X

def wordDelta {X : Type*} (t : List X) : ℓ²(List X, ℂ) := lp.single 2 t 1

lemma wordDelta_orthonormal (X : Type*) :
    Orthonormal ℂ (wordDelta (X := X)) := by
  apply orthonormal_iff_ite.mpr
  intro t s
  simp [wordDelta, lp.inner_single_left, lp.single_apply, Pi.single_apply]

def freeGroupRadialVector {X : Type*} (r : ℝ) (g : FreeGroup X) :
    ℓ²(List (X × Bool), ℂ) :=
  wordRadialFeature wordDelta r (Real.sqrt (1 - r ^ 2)) g⁻¹.toWord

lemma freeGroupRadialVector_inner {X : Type*} (r : ℝ) (hr : |r| ≤ 1)
    (g h : FreeGroup X) :
    ⟪freeGroupRadialVector r g, freeGroupRadialVector r h⟫_ℂ =
      ((r ^ (g * h⁻¹).toWord.length : ℝ) : ℂ) := by
  have hsq : (Real.sqrt (1 - r ^ 2)) ^ 2 = 1 - r ^ 2 := by
    apply Real.sq_sqrt
    have hb := (sq_le_sq₀ (abs_nonneg r) (by norm_num : (0 : ℝ) ≤ 1)).mpr hr
    simpa only [sq_abs, one_pow, sub_nonneg] using hb
  have he := wordRadialFeature_inner_eq
    (wordDelta (X := X × Bool))
    (wordDelta_orthonormal (X × Bool)) r (Real.sqrt (1 - r ^ 2)) hsq g⁻¹.toWord h⁻¹.toWord
  exact he.trans (congrArg (fun n : ℕ => ((r ^ n : ℝ) : ℂ)) (freeGroup_mul_inv_length g h).symm)

lemma freeGroupRadialVector_norm {X : Type*} (r : ℝ) (hr : |r| ≤ 1)
    (g : FreeGroup X) : ‖freeGroupRadialVector r g‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), freeGroupRadialVector_inner r hr]
  simp

theorem freeGroup_radial_factorization {X : Type*} (r : ℝ) (hr : |r| ≤ 1) :
    (∀ g : FreeGroup X, ‖freeGroupRadialVector r g‖ ≤ 1) ∧
    ∀ g h : FreeGroup X, ((r ^ (g*h⁻¹).toWord.length : ℝ) : ℂ) =
      ⟪freeGroupRadialVector r g, freeGroupRadialVector r h⟫_ℂ :=
  ⟨fun g => (freeGroupRadialVector_norm r hr g).le,
    fun g h => (freeGroupRadialVector_inner r hr g h).symm⟩
end CuntzPureness

end

end OAI
