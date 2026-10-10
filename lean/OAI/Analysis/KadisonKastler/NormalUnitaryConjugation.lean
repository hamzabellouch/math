import OAI.Analysis.KadisonKastler.NormalRepresentationRange
import OAI.Analysis.KadisonKastler.ConjugateFactor

namespace OAI

/-! # Bounded weak continuity of unitary representation changes -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem unitaryConj_coefficient (w : unitary (H →L[ℂ] H)) (a : H →L[ℂ] H) (x y : H) :
    inner ℂ y (unitaryConj w a x) =
      inner ℂ ((star (w : H →L[ℂ] H)) y) (a ((star (w : H →L[ℂ] H)) x)) := by
  change inner ℂ y ((w : H →L[ℂ] H) (a ((star (w : H →L[ℂ] H)) x))) = _
  exact (ContinuousLinearMap.adjoint_inner_left (w : H →L[ℂ] H)
    (a ((star (w : H →L[ℂ] H)) x)) y).symm

theorem unitaryConjugateEquiv_boundedWeakNormal (M : VonNeumannAlgebra H)
    (w : unitary (H →L[ℂ] H)) :
    BoundedWeakNormal M ((unitaryConjugateAlgebra w M).toStarSubalgebra.subtype.comp
      (unitaryConjugateEquiv w M).toStarAlgHom) := by
  intro ι l a b C _ hw x y
  change Tendsto (fun i => inner ℂ y (unitaryConj w (a i).val x)) l
    (𝓝 (inner ℂ y (unitaryConj w b.val x)))
  simpa only [unitaryConj_coefficient] using
    hw ((star (w : H →L[ℂ] H)) x) ((star (w : H →L[ℂ] H)) y)

end

end KadisonKastler

end OAI
