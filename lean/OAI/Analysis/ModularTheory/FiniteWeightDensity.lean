import OAI.Analysis.ModularTheory.FiniteWeightSpace
import OAI.Analysis.ModularTheory.CutoffTotality

namespace OAI

/-! Density of the concrete finite-weight GNS vectors. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def modularFiniteWeightCut (S : StandardModularData H)
    (a : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (ha : a ∈ modularCrossedProduct volume S) (n : ℕ) : modularFiniteWeightSpace S :=
  ⟨a * modularFiniteProjection n, mul_mem ha (modularFiniteProjection_mem S n),
    modularCoreSquareWeight_mul_finite S _ (modularFiniteProjection_finite S n) a⟩

lemma modularFiniteWeightMap_cut (S : StandardModularData H)
    (a : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (ha : a ∈ modularCrossedProduct volume S) (n : ℕ) :
    modularFiniteWeightMap S (modularFiniteWeightCut S a ha n) =
      a (modularCoreWeightVector S n) := by
  change modularWeightVector S (a * modularFiniteProjection n)
    (mul_mem ha (modularFiniteProjection_mem S n))
    (modularCoreSquareWeight_mul_finite S _ (modularFiniteProjection_finite S n) a) = _
  rw [modularWeightVector_mul S _ (modularFiniteProjection_mem S n)
    (modularFiniteProjection_finite S n) a ha, modularFiniteProjection_weightGNS]

lemma modularFiniteWeightMap_right_cut_tendsto (S : StandardModularData H)
    (T : modularFiniteWeightSpace S) :
    Tendsto (fun n => modularFiniteWeightMap S
      (modularFiniteWeightCut S T.val T.property.1 n)) atTop
      (𝓝 (modularFiniteWeightMap S T)) := by
  simp only [modularFiniteWeightMap_cut]
  exact modularWeightVector_tendsto S T.val T.property.1 T.property.2

lemma modularFiniteWeightMap_dense (S : StandardModularData H) :
    DenseRange (modularFiniteWeightMap S) := by
  change Dense ((LinearMap.range (modularFiniteWeightMap S)) : Set (Lp H 2 (volume : Measure ℝ)))
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro x hx
  have hz : (innerSL ℂ x) = 0 := by
    apply modularCutoff_annihilator_eq_zero S
    intro a ha n
    have he := hx (a (modularCoreWeightVector S n))
      (show a (modularCoreWeightVector S n) ∈ LinearMap.range (modularFiniteWeightMap S) from
        ⟨modularFiniteWeightCut S a ha n, modularFiniteWeightMap_cut S a ha n⟩)
    exact inner_eq_zero_symm.mp he
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have he := congrArg (fun T : Lp H 2 (volume : Measure ℝ) →L[ℂ] ℂ => T x) hz
  exact he

end WeakPureInfiniteness

end

end OAI
