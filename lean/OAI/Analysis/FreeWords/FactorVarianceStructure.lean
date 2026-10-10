import Mathlib
import OAI.Analysis.FreeWords.UnitaryTraceWitnessSupport

namespace OAI

noncomputable section

namespace KKFactorSupport

open KKUltraTrace

open scoped ComplexOrder InnerProductSpace

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end

end KKFactorSupport

namespace KKFactorSupport

open KKTraceTransfer KKUltraTrace

open scoped ComplexOrder InnerProductSpace BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance factorVarianceStructurePartialOrder (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance factorVarianceStructurePreorder (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance factorVarianceStructureLE (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance factorVarianceStructureStarOrderedRing (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

end

end KKFactorSupport

namespace KKFreeLiftFrontier

open KKTraceTransfer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end KKFreeLiftFrontier

namespace KKFactorSupport

open KKTraceTransfer KKUltraTrace

open scoped ComplexOrder InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance factorVarianceStructurePartialOrder_1 (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance factorVarianceStructurePreorder_1 (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance factorVarianceStructureLE_1 (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance factorVarianceStructureStarOrderedRing_1 (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

end

end KKFactorSupport

namespace KKFactorSupport

open KKTraceTransfer KKUltraTrace

open scoped ComplexOrder InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance factorVarianceStructurePartialOrder_2 (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance factorVarianceStructurePreorder_2 (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance factorVarianceStructureLE_2 (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance factorVarianceStructureStarOrderedRing_2 (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

end

end KKFactorSupport

namespace KKFactorSupport

open KKTraceTransfer KKUltraTrace

open scoped ComplexOrder InnerProductSpace

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance factorVarianceStructurePartialOrder_3 (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance factorVarianceStructurePreorder_3 (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance factorVarianceStructureLE_3 (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance factorVarianceStructureStarOrderedRing_3 (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem factor_trace_distance_bound {M : VonNeumannAlgebra H}
    (τ : FaithfulNormalTrace M) (hM : KKFreeLiftFrontier.IsFactor M) (x : ConcreteAlgebra M)
    (R : ℝ) (hR : ∀ u : unitary (ConcreteAlgebra M),
      ‖gnsVector (tracePositive τ) (x * (u : ConcreteAlgebra M) - (u : ConcreteAlgebra M) * x)‖ ≤ R) :
    ‖gnsVector (tracePositive τ) (x - τ.map x • 1)‖ ≤ R := by
  have ho : conjugacyOrbit τ x ⊆ Metric.closedBall (gnsVector (tracePositive τ) x) R := by
    rintro _ ⟨u,rfl⟩
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
    change ‖gnsVector (tracePositive τ) x - gnsVector (tracePositive τ) (algebraConj u x)‖ ≤ R
    rw [gnsVector_conj_sub_norm _ (tracePositive_tracial τ)]
    exact hR u
  have hh : conjugacyHull τ x ⊆ Metric.closedBall (gnsVector (tracePositive τ) x) R :=
    closure_minimal (convexHull_min ho (convex_closedBall _ _)) Metric.isClosed_closedBall
  have hv := hh (factor_trace_in_conjugacyHull τ hM x)
  rw [Metric.mem_closedBall, dist_comm, dist_eq_norm, ← map_sub] at hv
  exact hv

theorem factor_commutator_witness {M : VonNeumannAlgebra H}
    (τ : FaithfulNormalTrace M) (hM : KKFreeLiftFrontier.IsFactor M) (x : ConcreteAlgebra M) :
    ∃ u : unitary (ConcreteAlgebra M),
      ‖gnsVector (tracePositive τ) (x - τ.map x • 1)‖ ≤
        2 * ‖gnsVector (tracePositive τ) (x * (u : ConcreteAlgebra M) - (u : ConcreteAlgebra M) * x)‖ := by
  by_cases hz : ‖gnsVector (tracePositive τ) (x - τ.map x • 1)‖ = 0
  · exact ⟨1, by rw [hz]; positivity⟩
  · by_contra! hall
    have hb := factor_trace_distance_bound τ hM x
      (‖gnsVector (tracePositive τ) (x - τ.map x • 1)‖ / 2)
      (fun u => by linarith [hall u])
    have hn := norm_nonneg (gnsVector (tracePositive τ) (x - τ.map x • 1))
    exact hz (by linarith)

end

end KKFactorSupport
end

end OAI
