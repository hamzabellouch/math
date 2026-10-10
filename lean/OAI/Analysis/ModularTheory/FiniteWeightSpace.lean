import OAI.Analysis.ModularTheory.CoreTracial

namespace OAI

/-! The finite-square-weight domain and its concrete Hilbert-space map.
The norm on its image is the actual modular L² norm. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularCoreSquareWeight_smul_finite (S : StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : modularCoreSquareWeight S T < ⊤) (c : ℂ) :
    modularCoreSquareWeight S (c • T) < ⊤ := by
  have h := modularCoreSquareWeight_mul_finite S T hT
    (c • (1 : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)))
  simpa only [smul_mul_assoc, one_mul] using h

lemma modularCoreSquareWeight_star_finite (S : StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct volume S)
    (hfin : modularCoreSquareWeight S T < ⊤) :
    modularCoreSquareWeight S (star T) < ⊤ := by
  rwa [modularCoreSquareWeight_adjoint S T hT]

def modularFiniteWeightSpace (S : StandardModularData H) :
    Submodule ℂ (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) where
  carrier := {T | T ∈ modularCrossedProduct volume S ∧ modularCoreSquareWeight S T < ⊤}
  zero_mem' := ⟨zero_mem _, by simp⟩
  add_mem' hR hT := ⟨add_mem hR.1 hT.1,
    modularCoreSquareWeight_add_finite S _ hT.2 _ hR.2⟩
  smul_mem' c T hT := ⟨(modularCrossedProduct volume S).toStarSubalgebra.smul_mem hT.1 c,
    modularCoreSquareWeight_smul_finite S T hT.2 c⟩

lemma modularWeightVector_smul (S : StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct volume S)
    (hfin : modularCoreSquareWeight S T < ⊤) (c : ℂ) :
    modularWeightVector S (c • T)
      ((modularCrossedProduct volume S).toStarSubalgebra.smul_mem hT c)
      (modularCoreSquareWeight_smul_finite S T hfin c) =
        c • modularWeightVector S T hT hfin := by
  apply tendsto_nhds_unique (modularWeightVector_tendsto S (c • T) _ _)
  simpa only [smul_apply] using
    (modularWeightVector_tendsto S T hT hfin).const_smul c

def modularFiniteWeightMap (S : StandardModularData H) :
    modularFiniteWeightSpace S →ₗ[ℂ] Lp H 2 (volume : Measure ℝ) where
  toFun T := modularWeightVector S T.val T.property.1 T.property.2
  map_add' R T := modularWeightVector_add S T.val T.property.1 T.property.2
    R.val R.property.1 R.property.2
  map_smul' c T := modularWeightVector_smul S T.val T.property.1 T.property.2 c

lemma modularFiniteWeightMap_injective (S : StandardModularData H) :
    Function.Injective (modularFiniteWeightMap S) := by
  intro T R h
  have hz : modularFiniteWeightMap S (T - R) = 0 := by
    calc
      modularFiniteWeightMap S (T - R) =
          modularFiniteWeightMap S T - modularFiniteWeightMap S R :=
        map_sub (modularFiniteWeightMap S) T R
      _ = 0 := sub_eq_zero.mpr h
  have he : (T - R).val = 0 :=
    (modularWeightVector_eq_zero_iff S _ (T - R).property.1 (T - R).property.2).mp hz
  apply Subtype.ext
  exact sub_eq_zero.mp he

lemma modularWeightVector_star_norm (S : StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct volume S)
    (hfin : modularCoreSquareWeight S T < ⊤) :
    ‖modularWeightVector S (star T) (star_mem hT)
      (modularCoreSquareWeight_star_finite S T hT hfin)‖ =
        ‖modularWeightVector S T hT hfin‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [modularWeightVector_norm_sq, modularWeightVector_norm_sq,
    modularCoreSquareWeight_adjoint S T hT]

end WeakPureInfiniteness

end

end OAI
