import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousComplexification
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFiniteRankStep

namespace OAI

/-! # Complexification preserves the finite-rank remainder

The range embeds into two copies of the original real finite-dimensional
range by the explicit real and imaginary coordinate maps.
-/

namespace DefocusingNLS

theorem homogeneousComplexification_finiteRank (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (K : HomogeneousY a k →L[ℝ] HomogeneousY a k)
    (hK : FiniteDimensional ℝ (LinearMap.range K.toLinearMap)) :
    FiniteDimensional ℂ
      (LinearMap.range (homogeneousComplexification a k ha ha1 hk K).toLinearMap) := by
  let V := LinearMap.range K.toLinearMap
  let R := LinearMap.range (homogeneousComplexification a k ha ha1 hk K).toLinearMap
  let X := homogeneousComplexReal a k ha ha1 hk
  let Y := homogeneousComplexImag a k ha ha1 hk
  let : FiniteDimensional ℝ V := hK
  have hX (v : R) : X v.val ∈ V := by
    obtain ⟨z, hz⟩ := v.prop
    rw [← hz]
    change homogeneousComplexReal a k ha ha1 hk
      (homogeneousComplexification a k ha ha1 hk K z) ∈ V
    rw [homogeneousComplexification_real]
    exact ⟨X z, rfl⟩
  have hY (v : R) : Y v.val ∈ V := by
    obtain ⟨z, hz⟩ := v.prop
    rw [← hz]
    change homogeneousComplexImag a k ha ha1 hk
      (homogeneousComplexification a k ha ha1 hk K z) ∈ V
    rw [homogeneousComplexification_imag]
    exact ⟨Y z, rfl⟩
  let F : R →ₗ[ℝ] V × V :=
    { toFun := fun v => (⟨X v.val, hX v⟩, ⟨Y v.val, hY v⟩)
      map_add' := by
        intro u v
        apply Prod.ext <;> apply Subtype.ext <;> exact map_add _ _ _
      map_smul' := by
        intro c v
        apply Prod.ext <;> apply Subtype.ext <;> exact map_smul _ _ _ }
  have hF : Function.Injective F := by
    intro u v huv
    have hx : X u.val = X v.val :=
      congrArg (fun z : V × V => (z.1 : HomogeneousY a k)) huv
    have hy : Y u.val = Y v.val :=
      congrArg (fun z : V × V => (z.2 : HomogeneousY a k)) huv
    apply Subtype.ext
    apply Prod.ext
    · rw [← homogeneousComplexCoordinates_first a k ha ha1 hk u.val,
        ← homogeneousComplexCoordinates_first a k ha ha1 hk v.val]
      exact congrArg₂ (fun x y => x + Complex.I • y) hx hy
    · rw [← homogeneousComplexCoordinates_second a k ha ha1 hk u.val,
        ← homogeneousComplexCoordinates_second a k ha ha1 hk v.val]
      exact congrArg₂ (fun x y => homogeneousConjugation a k ha ha1 hk x +
        Complex.I • homogeneousConjugation a k ha ha1 hk y) hx hy
  let : FiniteDimensional ℝ R := FiniteDimensional.of_injective F hF
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ R

end DefocusingNLS

end OAI
