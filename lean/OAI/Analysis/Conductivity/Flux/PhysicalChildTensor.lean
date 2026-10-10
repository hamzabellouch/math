import Mathlib
import OAI.Analysis.Conductivity.Branching.ChildCentralL2

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def sourceChildTensorPush (k : Fin 2)
    (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => sourceScale⁻¹ *
    A ((sourceChildHomeomorph (actualChildSign k)).symm y) (childAxis i) (childAxis j)

lemma sourceChildTensorPush_symmetric (k : Fin 2)
    (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ y,(A y).IsSymm) (y : Fin 3 → ℝ) :
    (sourceChildTensorPush k A y).IsSymm := by
  ext i j
  exact congrArg (fun z : ℝ => sourceScale⁻¹*z)
    (congrFun (congrFun (hA ((sourceChildHomeomorph (actualChildSign k)).symm y))
      (childAxis i)) (childAxis j))

lemma sourceChildTensorPush_mixed (k : Fin 2)
    (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (y g v : Fin 3 → ℝ) :
    sourceScale^3 *
      ((fun i => sourceScale⁻¹*g (childAxis i)) ⬝ᵥ
        (sourceChildTensorPush k A (sourceChildCoordinates (actualChildSign k) y)*ᵥv))=
      g ⬝ᵥ (A y*ᵥ(fun i => sourceScale*v (childAxis i))) := by
  have he : (sourceChildHomeomorph (actualChildSign k)).symm
      (sourceChildCoordinates (actualChildSign k) y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply y
  simp only [sourceChildTensorPush,he,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  have h₀ : childAxis 0=1 := rfl
  have h₁ : childAxis 1=0 := rfl
  have h₂ : childAxis 2=2 := rfl
  simp only [h₀,h₁,h₂]
  norm_num [sourceScale]
  ring

lemma sourceChildTensorPush_quadratic (k : Fin 2)
    (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (y v : Fin 3 → ℝ) :
    v ⬝ᵥ (sourceChildTensorPush k A y*ᵥv)=
      sourceScale⁻¹*((fun i => v (childAxis i)) ⬝ᵥ
        (A ((sourceChildHomeomorph (actualChildSign k)).symm y)*ᵥ
          (fun i => v (childAxis i)))) := by
  simp only [sourceChildTensorPush,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  simp [childAxis]
  ring

lemma childAxis_norm_sq (v : Fin 3 → ℝ) :
    (∑ i : Fin 3,(v (childAxis i))^2)=∑ i : Fin 3,(v i)^2 := by
  simp only [Fin.sum_univ_three]
  simp [childAxis]
  ring

lemma sourceChildTensorPush_elliptic (k : Fin 2)
    (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (c C : ℝ)
    (hA : ∀ y v,c*(∑ i : Fin 3,(v i)^2)≤v ⬝ᵥ (A y*ᵥv) ∧
      v ⬝ᵥ (A y*ᵥv)≤C*(∑ i : Fin 3,(v i)^2)) (y v : Fin 3 → ℝ) :
    (sourceScale⁻¹*c)*(∑ i : Fin 3,(v i)^2)≤
        v ⬝ᵥ (sourceChildTensorPush k A y*ᵥv) ∧
      v ⬝ᵥ (sourceChildTensorPush k A y*ᵥv)≤
        (sourceScale⁻¹*C)*(∑ i : Fin 3,(v i)^2) := by
  rw [sourceChildTensorPush_quadratic]
  have hh := hA ((sourceChildHomeomorph (actualChildSign k)).symm y)
    (fun i => v (childAxis i))
  rw [childAxis_norm_sq] at hh
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh.1
      (show 0 ≤ sourceScale⁻¹ by norm_num [sourceScale])
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh.2
      (show 0 ≤ sourceScale⁻¹ by norm_num [sourceScale])

end ScalarConductivity

end
end

end OAI
