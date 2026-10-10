import OAI.Analysis.Cuntz.Content
import OAI.Analysis.Cuntz.RegularizedState

namespace OAI

noncomputable section

/-! Commutative dimension contents and continuous positive functions. -/

section
open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] Classical.propDecidable
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A X : Type*} [CStarAlgebra A] [TopologicalSpace X]

/-- Transport the existing regularized dimension through a real star algebra
homomorphism. On negative functions the auxiliary value is zero and is unused. -/
def CuntzDimensionState.continuousDimension (d : CuntzDimensionState A) {n : ℕ}
    (φ : C(X, ℝ) →⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) A) : PositiveDimensionFunctional X where
  toFun f := if hf : 0 ≤ f then d.regularized ⟨n, CStarMatrix.ofMatrix.symm (φ f), map_nonneg φ hf⟩ else 0
  nonneg f hf := by simp only [dite_eq_left hf]; exact d.regularized_nonneg _
  mono f g hf hfg := by
    simp only [dite_eq_left hf, dite_eq_left (hf.trans hfg)]
    exact d.regularized_mono (cuntzLE_of_nonneg_le (map_nonneg φ hf) (OrderHomClass.mono φ hfg))
  subadd f g hf hg := by
    simp only [dite_eq_left hf, dite_eq_left hg, dite_eq_left (add_nonneg hf hg), map_add]
    exact d.regularized_sum_le _ _ (map_nonneg φ hf) (map_nonneg φ hg)
  orthogonal f g hf hg hfg := by
    simp only [dite_eq_left hf, dite_eq_left hg, dite_eq_left (add_nonneg hf hg), map_add]
    apply d.regularized_orthogonal_add _ _ (map_nonneg φ hf) (map_nonneg φ hg)
    rw [← map_mul, hfg, map_zero]

@[simp] theorem CuntzDimensionState.continuousDimension_apply (d : CuntzDimensionState A) {n : ℕ}
    (φ : C(X, ℝ) →⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) A) (f : C(X, ℝ)) (hf : 0 ≤ f) :
    (d.continuousDimension φ).toFun f =
      d.regularized ⟨n, CStarMatrix.ofMatrix.symm (φ f), map_nonneg φ hf⟩ := by
  simp [continuousDimension, hf]

/-- A compact content constructed from the SAME ambient dimension state. -/
def CuntzDimensionState.commutativeContent (d : CuntzDimensionState A) [NormalSpace X] {n : ℕ}
    (φ : C(X, ℝ) →⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) A) : MeasureTheory.Content X :=
  (d.continuousDimension φ).content

theorem CuntzDimensionState.continuousDimension_one (d : CuntzDimensionState A) {n : ℕ}
    (φ : C(X, ℝ) →⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) A) :
    (d.continuousDimension φ).toFun 1 = n := by
  rw [d.continuousDimension_apply φ 1 zero_le_one]
  rw [← d.regularized_unit n]
  apply d.regularized_eq
  change CuntzEquivalent (CStarMatrix.ofMatrix.symm (φ 1)) 1
  rw [map_one]
  exact .refl _

end Kaplansky

end

open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A X : Type*} [CStarAlgebra A] [TopologicalSpace X]
namespace CuntzDimensionState

theorem continuousDimension_scaleInvariant (d : CuntzDimensionState A) {n : ℕ}
    (φ : C(X, ℝ) →⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) A) :
    (d.continuousDimension φ).ScaleInvariant := by
  intro f hf r hr
  rw [d.continuousDimension_apply φ f hf,
    d.continuousDimension_apply φ (r • f) (fun x => mul_nonneg hr.le (hf x))]
  apply d.regularized_eq
  change CuntzEquivalent (CStarMatrix.ofMatrix.symm (φ (r • f))) _
  rw [map_smul]
  exact cuntzEquivalent_pos_smul (φ f) hr

theorem continuousDimension_lowerSemicontinuous (d : CuntzDimensionState A) {n : ℕ}
    (φ : C(X, ℝ) →⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) A) (hφ : Continuous φ) :
    (d.continuousDimension φ).ConeLowerSemicontinuous := by
  let g : {f : C(X, ℝ) // 0 ≤ f} → {a : CStarMatrix (Fin n) (Fin n) A // 0 ≤ a} :=
    fun f => ⟨φ f.val, map_nonneg φ f.property⟩
  have hg : Continuous g := (hφ.comp continuous_subtype_val).subtype_mk _
  have h := (d.regularized_lowerSemicontinuous n).comp hg
  change LowerSemicontinuous (fun f : {f : C(X, ℝ) // 0 ≤ f} => (d.continuousDimension φ).toFun f.val)
  have he : (fun f : {f : C(X, ℝ) // 0 ≤ f} => (d.continuousDimension φ).toFun f.val) =
      (fun f : {f : C(X, ℝ) // 0 ≤ f} => d.regularized ⟨n, CStarMatrix.ofMatrix.symm (φ f.val), map_nonneg φ f.property⟩) := by
    funext f
    exact d.continuousDimension_apply φ f.val f.property
  rw [he]
  exact h

variable [CompactSpace X] [NormalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]

/-- The measure of a positive support is the actual regularized ambient
Cuntz dimension of its image, with no functional or measure-existence premise. -/
theorem continuousDimension_measure_positive_support (d : CuntzDimensionState A) {n : ℕ}
    (φ : C(X, ℝ) →⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) A) (hφ : Continuous φ)
    (f : C(X, ℝ)) (hf : 0 ≤ f) :
    (d.continuousDimension φ).measure {x | 0 < f x} =
      ENNReal.ofReal (d.regularized ⟨n, CStarMatrix.ofMatrix.symm (φ f), map_nonneg φ hf⟩) := by
  rw [← d.continuousDimension_apply φ f hf]
  exact (d.continuousDimension φ).measure_positive_support
    (d.continuousDimension_scaleInvariant φ) (d.continuousDimension_lowerSemicontinuous φ hφ) f hf

end CuntzDimensionState
end Kaplansky

end

end OAI
