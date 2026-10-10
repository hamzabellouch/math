import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularPhysicalBasis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace OAI

/-! The four physical matching columns and their exact determinant criterion. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)
local notation "J₄" => Fin 2 × Fin 2

noncomputable def spectralStateCoordinates : E₄ ≃ₗ[ℂ] (J₄ → ℂ) where
  toFun Z i := ![![Z.1.1,Z.1.2],![Z.2.1,Z.2.2]] i.1 i.2
  invFun f := ((f (0,0),f (0,1)),(f (1,0),f (1,1)))
  left_inv _ := rfl
  right_inv f := by
    funext ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> rfl
  map_add' Z W := by
    funext ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> rfl
  map_smul' a Z := by
    funext ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> rfl

noncomputable def spectralMatchingColumns (R₀ R₁ O₀ O₁ : E₄) : J₄ → E₄ :=
  fun i => ![![R₀,R₁],![O₀,O₁]] i.1 i.2

noncomputable def spectralMatchingMatrix (R₀ R₁ O₀ O₁ : E₄) : Matrix J₄ J₄ ℂ :=
  fun i j => spectralStateCoordinates (spectralMatchingColumns R₀ R₁ O₀ O₁ j) i

noncomputable def spectralMatchingDeterminant (R₀ R₁ O₀ O₁ : E₄) : ℂ :=
  (spectralMatchingMatrix R₀ R₁ O₀ O₁).det

theorem spectralMatchingDeterminant_ne_zero_iff (R₀ R₁ O₀ O₁ : E₄) :
    spectralMatchingDeterminant R₀ R₁ O₀ O₁ ≠ 0 ↔
      LinearIndependent ℂ (spectralMatchingColumns R₀ R₁ O₀ O₁) := by
  have hM : spectralMatchingDeterminant R₀ R₁ O₀ O₁ ≠ 0 ↔
      LinearIndependent ℂ (spectralMatchingMatrix R₀ R₁ O₀ O₁).col := by
    rw [spectralMatchingDeterminant,← isUnit_iff_ne_zero,
      ← Matrix.isUnit_iff_isUnit_det,← Matrix.linearIndependent_cols_iff_isUnit]
  exact hM.trans (spectralStateCoordinates.toLinearMap.linearIndependent_iff
    (LinearMap.ker_eq_bot.mpr spectralStateCoordinates.injective))

theorem spectralMatchingDeterminant_zero_iff (R₀ R₁ O₀ O₁ : E₄) :
    spectralMatchingDeterminant R₀ R₁ O₀ O₁=0 ↔
      ∃ a b c d : ℂ, a • R₀+b • R₁+c • O₀+d • O₁=0 ∧
        (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) := by
  have hz : spectralMatchingDeterminant R₀ R₁ O₀ O₁=0 ↔
      ¬ LinearIndependent ℂ (spectralMatchingColumns R₀ R₁ O₀ O₁) := by
    simpa only [not_not] using not_congr (spectralMatchingDeterminant_ne_zero_iff R₀ R₁ O₀ O₁)
  rw [hz,Fintype.not_linearIndependent_iff]
  constructor
  · rintro ⟨g,hg,⟨⟨i,j⟩,hne⟩⟩
    refine ⟨g (0,0),g (0,1),g (1,0),g (1,1),?_,?_⟩
    · simpa only [Fintype.sum_prod_type,Fin.sum_univ_two,spectralMatchingColumns,
        Matrix.cons_val_zero,Matrix.cons_val_one,add_assoc] using hg
    · fin_cases i <;> fin_cases j <;> tauto
  · rintro ⟨a,b,c,d,he,hne⟩
    let g : J₄ → ℂ := fun i => ![![a,b],![c,d]] i.1 i.2
    refine ⟨g,?_,?_⟩
    · simpa only [Fintype.sum_prod_type,Fin.sum_univ_two,spectralMatchingColumns,g,
        Matrix.cons_val_zero,Matrix.cons_val_one,add_assoc] using he
    · rcases hne with ha | hb | hc | hd
      · exact ⟨(0,0),ha⟩
      · exact ⟨(0,1),hb⟩
      · exact ⟨(1,0),hc⟩
      · exact ⟨(1,1),hd⟩

end DefocusingNLS

end OAI
