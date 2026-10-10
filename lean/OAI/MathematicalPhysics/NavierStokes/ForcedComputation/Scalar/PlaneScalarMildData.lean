import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildSource
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildSmooth
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCoefficientJets

namespace OAI

/-! Compatible data turn the finite-jet equations into one scalar mild solution. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild

open Set ShearFlows
open scoped Topology ContDiff

/-- Initial data, source, and the three coefficients, represented consistently at every order. -/
structure CompatibleData (T : ℝ) where
  initial : ∀ k, Jet k
  source : ∀ k, WeaklySingular.Path (Jet k) T
  coefficient : ∀ k, Fin 3 → C(Icc (0 : ℝ) T, Jet k)
  initial_truncate : ∀ k n (hkn : k ≤ n),
    BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (initial n) = initial k
  source_truncate : ∀ k n (hkn : k ≤ n), truncatePath k n hkn T (source n) = source k
  coefficient_truncate : ∀ k n (hkn : k ≤ n) i t,
    BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (coefficient n i t) = coefficient k i t

namespace CompatibleData

/-- Equality of represented scalar functions supplies compatibility automatically. -/
def ofRepresentatives {T : ℝ} (w₀ : Plane → ℝ) (h : Icc (0 : ℝ) T → Plane → ℝ)
    (b : Fin 3 → Icc (0 : ℝ) T → Plane → ℝ)
    (J : ∀ k, Jet k) (g : ∀ k, WeaklySingular.Path (Jet k) T)
    (c : ∀ k, Fin 3 → C(Icc (0 : ℝ) T, Jet k))
    (hJ : ∀ k x, BoundedSpatialJets.function Plane ℝ k (J k) x = w₀ x)
    (hg : ∀ k t x, BoundedSpatialJets.function Plane ℝ k (g k t) x = h t x)
    (hc : ∀ k i t x, BoundedSpatialJets.function Plane ℝ k (c k i t) x = b i t x) :
    CompatibleData T where
  initial := J
  source := g
  coefficient := c
  initial_truncate := by
    intro k n hkn
    apply BoundedSpatialJets.function_injective Plane ℝ k
    ext x
    change BoundedSpatialJets.function Plane ℝ k
      (BoundedSpatialJets.truncate Plane ℝ k n hkn (J n)) x = _
    rw [BoundedSpatialJets.function_truncate, hJ, hJ]
  source_truncate := by
    intro k n hkn
    apply truncatePath_eq_of_functions k n hkn T
    intro t x
    exact (hg n t x).trans (hg k t x).symm
  coefficient_truncate := by
    intro k n hkn i t
    apply coefficient_truncate_of_functions k n hkn T (c n i) (c k i)
    intro s x
    exact (hc n i s x).trans (hc k i s x).symm

/-- The canonical affine term includes the prescribed initial data and actual heat source. -/
def affinePath {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν) (D : CompatibleData T) (k : ℕ) :
    WeaklySingular.Path (Jet k) T :=
  forcingPath hT hν k (D.initial (k+1)) (D.source k)

theorem affinePath_truncate {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k n : ℕ) (hkn : k ≤ n) :
    truncatePath k n hkn T (D.affinePath hT hν n) = D.affinePath hT hν k := by
  have hJ : BoundedSpatialJets.truncateCLM Plane ℝ k n hkn
      (BoundedSpatialJets.truncate Plane ℝ n (n+1) (by omega) (D.initial (n+1))) =
      BoundedSpatialJets.truncate Plane ℝ k (k+1) (by omega) (D.initial (k+1)) := by
    calc
      _ = BoundedSpatialJets.truncateCLM Plane ℝ k n hkn (D.initial n) :=
        congrArg (BoundedSpatialJets.truncateCLM Plane ℝ k n hkn)
          (D.initial_truncate n (n+1) (by omega))
      _ = D.initial k := D.initial_truncate k n hkn
      _ = _ := (D.initial_truncate k (k+1) (by omega)).symm
  exact (forcingPath_truncate hT hν k n hkn _ _ hJ (D.source n)).trans
    (congrArg (forcingPath hT hν k (D.initial (k+1))) (D.source_truncate k n hkn))

/-- All finite-order solutions determine this one scalar function. -/
def solution {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν) (D : CompatibleData T)
    (t : Icc (0 : ℝ) T) (x : Plane) : ℝ :=
  commonFunction hT hν D.coefficient (D.affinePath hT hν) t x

theorem solution_smooth {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (D.solution hT hν t) :=
  commonFunction_smooth hT hν D.coefficient (D.affinePath hT hν)
    D.coefficient_truncate (D.affinePath_truncate hT hν) t

theorem solution_spatial_bound {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : Icc (0 : ℝ) T, ∀ x : Plane,
      ‖iteratedFDeriv ℝ k (D.solution hT hν t) x‖ ≤ C :=
  commonFunction_spatial_bound hT hν D.coefficient (D.affinePath hT hν)
    D.coefficient_truncate (D.affinePath_truncate hT hν) k

theorem solution_spatial_continuous {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (k : ℕ) :
    Continuous (fun p : Icc (0 : ℝ) T × Plane =>
      iteratedFDeriv ℝ k (D.solution hT hν p.1) p.2) :=
  commonFunction_spatial_continuous hT hν D.coefficient (D.affinePath hT hν)
    D.coefficient_truncate (D.affinePath_truncate hT hν) k

end CompatibleData
end ForcedComputation.PlaneScalarMild

end

end OAI
