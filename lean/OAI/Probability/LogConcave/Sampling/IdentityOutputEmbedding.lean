import Mathlib
import OAI.Probability.LogConcave.Sampling.ProbabilityNodes
import OAI.Probability.LogConcave.Complexity.CenteringStateBudget

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

local instance identityOutputEmbeddingDecidableEqUnit : DecidableEq Unit :=
  Classical.decEq _

def identityOutputEmbedding (d : ℕ) : Fin d ↪ (Unit → Fin d) :=
  ⟨fun i _ => i,fun _ _ h => congrFun h ()⟩

def identityOutputProjection (d : ℕ) : EuclideanSpace ℝ (Unit → Fin d) →L[ℝ] Point d :=
  finiteCoordinateProjection (identityOutputEmbedding d)

lemma identityOutputProjection_vector {d : ℕ} (f : Point d → Point d) (y : Point d) :
    identityOutputProjection d (tensorVector (vectorArray f) y)=f y := by
  ext i
  change inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i) (f y)=_
  simp only [EuclideanSpace.basisFun_inner]

lemma identityOutputProjection_lie {d : ℕ} (H : Point d → ℝ)
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c))
    (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
      -A (Sum.elim (fun _ => z) (fun _ => i)) y) (y : Point d) :
    identityOutputProjection d (tensorVector
      (iterTensorLie H A (vectorArray (id : Point d → Point d)) 1) y)=skewLieField H A y := by
  ext i
  change tensorLie H A (vectorArray (id : Point d → Point d)) (fun _ => i) y=_
  rw [tensorLie_eq_directional H A _ (fun c => (hA c).smooth)
    (fun c => (identityArray_polySmooth d c).smooth) hsk]
  change fderiv ℝ ((innerSL ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)) : Point d → ℝ) y
    (skewLieField H A y)=_
  rw [ContinuousLinearMap.fderiv]
  simp only [innerSL_apply_apply, EuclideanSpace.basisFun_inner]

lemma projection_chainTaylor {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] G) (J : ℕ → ℝ → E) (n : ℕ) (a b : ℝ) :
    L (chainTaylor J n a b)=chainTaylor (fun k t => L (J k t)) n a b := by
  simp only [chainTaylor,map_sum,map_smul]

lemma projection_rms {Ω I J : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype I] [Fintype J] (e : I ↪ J)
    {f : Ω → EuclideanSpace ℝ J} (hm : Measurable f)
    {B : ℝ} (hi : Integrable (fun y => ‖f y‖^2) μ) (hb : (∫y,‖f y‖^2 ∂μ)≤B) :
    Integrable (fun y => ‖finiteCoordinateProjection e (f y)‖^2) μ ∧
      (∫y,‖finiteCoordinateProjection e (f y)‖^2 ∂μ)≤B := by
  have ha (y : Ω) : ‖finiteCoordinateProjection e (f y)‖^2≤‖f y‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (finiteCoordinateProjection_norm_le _ _) 2
  have h := hi.mono' (((finiteCoordinateProjection e).continuous.measurable.comp hm).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs,abs_sq,Function.comp_def] using ha y))
  exact ⟨h,(integral_mono h hi ha).trans hb⟩
end LogConcaveSampling

end

end

end OAI
