import OAI.Analysis.Pureness.Quasitrace.NormalizedQuasitraceCarrier
import Mathlib.Analysis.Convex.KreinMilman

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def additiveQuasitraceCoordinates : Set (QuasitraceCoordinates A) :=
  {p | ∀ x y : A, p.1 (x + y) = p.1 x + p.1 y}

omit [PartialOrder A] [StarOrderedRing A] in
lemma isClosed_additiveQuasitraceCoordinates :
    IsClosed (additiveQuasitraceCoordinates (A := A)) := by
  exact isClosed_forall_pointwise _ fun x => isClosed_forall_pointwise _ fun y =>
    isClosed_eq ((continuous_apply (x + y)).comp continuous_fst)
      (((continuous_apply x).comp continuous_fst).add ((continuous_apply y).comp continuous_fst))

omit [PartialOrder A] [StarOrderedRing A] in
lemma convex_additiveQuasitraceCoordinates :
    Convex ℝ (additiveQuasitraceCoordinates (A := A)) := by
  intro p hp q hq a b ha hb hab x y
  change (a : ℂ) * p.1 (x + y) + (b : ℂ) * q.1 (x + y) =
    ((a : ℂ) * p.1 x + (b : ℂ) * q.1 x) + ((a : ℂ) * p.1 y + (b : ℂ) * q.1 y)
  rw [hp x y, hq x y]
  ring

theorem normalizedQuasitraceCarrier_eq_closure_extremePoints :
    normalizedQuasitraceCarrier (A := A) =
      closure (convexHull ℝ ((normalizedQuasitraceCarrier (A := A)).extremePoints ℝ)) :=
  (closure_convexHull_extremePoints isCompact_normalizedQuasitraceCarrier
    convex_normalizedQuasitraceCarrier).symm

theorem exists_extreme_normalizedQuasitrace (T : TwoQuasitrace A) (hT : T.base 1 = 1) :
    ((normalizedQuasitraceCarrier (A := A)).extremePoints ℝ).Nonempty :=
  isCompact_normalizedQuasitraceCarrier.extremePoints_nonempty ⟨T.coordinates, T.coordinates_mem hT⟩

theorem normalizedQuasitrace_additive_of_extremePoints
    (h : (normalizedQuasitraceCarrier (A := A)).extremePoints ℝ ⊆ additiveQuasitraceCoordinates)
    (T : TwoQuasitrace A) (hT : T.base 1 = 1) :
    ∀ x y : A, T.base (x + y) = T.base x + T.base y := by
  have hc : normalizedQuasitraceCarrier (A := A) ⊆ additiveQuasitraceCoordinates := by
    rw [normalizedQuasitraceCarrier_eq_closure_extremePoints]
    exact closure_minimal (convexHull_min h convex_additiveQuasitraceCoordinates)
      isClosed_additiveQuasitraceCoordinates
  exact hc (T.coordinates_mem hT)
end CuntzPureness

end

end OAI
