import Mathlib
import OAI.Analysis.FreeWords.PartialUnitaryNorm
import OAI.Analysis.FreeWords.PartialUnitaryOrder
import OAI.Analysis.FreeWords.ProjectionRound

namespace OAI

noncomputable section

namespace KKLocalPatching.PartialUnitary

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKProjectionSupport

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)

local instance partialUnitaryTraceConcreteOrder : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance partialUnitaryTraceConcretePreorder : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance partialUnitaryTraceConcreteLE : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance partialUnitaryTraceConcreteSOR : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem power_dist_sq {v w : PartialUnitary (ConcreteAlgebra M)} (h : v≤w) (k : ℤ) :
    dist (gnsVector (tracePositive τ) (v.power k)) (gnsVector (tracePositive τ) (w.power k))^2 =
      (τ.map w.support).re-(τ.map v.support).re := by
  have hh := congrArg Complex.re (traceNorm_sq τ (w.power k-v.power k))
  simp only [Complex.ofReal_re,difference_square h,map_sub,Complex.sub_re] at hh
  rw [dist_comm,dist_eq_norm,← map_sub,← traceNorm_eq_gns]
  exact hh

theorem support_trace_mono {v w : PartialUnitary (ConcreteAlgebra M)} (h : v≤w) :
    (τ.map v.support).re≤(τ.map w.support).re := by
  have hsq := power_dist_sq τ h 0
  nlinarith [sq_nonneg (dist (gnsVector (tracePositive τ) (v.power 0)) (gnsVector (tracePositive τ) (w.power 0)))]

theorem support_trace_le_one (v : PartialUnitary (ConcreteAlgebra M)) :
    (τ.map v.support).re≤1 := by
  rw [← traceNorm_projection_sq τ v.projection]
  have h := (traceNorm_le_norm τ v.support).trans v.norm_support_le_one
  nlinarith [traceNorm_nonneg τ v.support]

end

end KKLocalPatching.PartialUnitary
end

end OAI
