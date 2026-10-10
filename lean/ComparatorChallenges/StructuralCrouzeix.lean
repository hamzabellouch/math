import Mathlib

namespace OAI

universe u_61 u_63 u_67 u_83 u_84 u_181

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace CompleteCrouzeix



def numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Set ℂ :=
  {z | ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
    inner ℂ x (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x) = z}

end CompleteCrouzeix

namespace CompleteCrouzeix
open Set Filter Metric Complex
open scoped Topology


structure DiskCoordinate (U : Set ℂ) (a : ℂ) where
  outer : Set ℂ
  outer_open : IsOpen outer
  closure_subset : closure U ⊆ outer
  toDisk : ℂ → ℂ
  fromDisk : ℂ → ℂ
  analytic_to : AnalyticOnNhd ℂ toDisk outer
  injective_to : InjOn toDisk outer
  noncritical_to : ∀ z ∈ outer, deriv toDisk z ≠ 0
  image_open : IsOpen (toDisk '' outer)
  analytic_from : AnalyticOnNhd ℂ fromDisk (toDisk '' outer)
  inverse_map : MapsTo fromDisk (toDisk '' outer) outer
  left_inverse : ∀ z ∈ outer, fromDisk (toDisk z) = z
  right_inverse : ∀ w ∈ toDisk '' outer, toDisk (fromDisk w) = w
  closedDisk_subset : closedBall 0 1 ⊆ toDisk '' outer
  image_domain : toDisk '' U = ball 0 1
  base_zero : toDisk a = 0

end CompleteCrouzeix

namespace CompleteCrouzeix
open Set Filter Metric Complex
open scoped Topology


def exteriorMap (a b : ℂ) (h : ℂ → ℂ) (t : ℂ) : ℂ := a*t+b+h t⁻¹

structure ExteriorCoordinate (U : Set ℂ) where
  radius : ℝ
  radius_gt : 1 < radius
  leading : ℂ
  constant : ℂ
  regular : ℂ → ℂ
  leading_ne : leading ≠ 0
  analytic_regular : AnalyticOnNhd ℂ regular (ball 0 radius)
  injective : InjOn (exteriorMap leading constant regular) {t | radius⁻¹ < ‖t‖}
  noncritical : ∀ t, radius⁻¹ < ‖t‖ → deriv (exteriorMap leading constant regular) t ≠ 0
  boundary_image : exteriorMap leading constant regular '' sphere 0 1 = frontier U
  interior_iff : ∀ t, radius⁻¹ < ‖t‖ →
    (exteriorMap leading constant regular t ∈ U ↔ t ∈ ball 0 1)
  outside : ∀ t, 1 < ‖t‖ → exteriorMap leading constant regular t ∉ closure U

end CompleteCrouzeix

namespace CompleteCrouzeix
open Polynomial Finset
variable {A : Type u_61} [Ring A] [Algebra ℂ A]

def scalarJetEval (β : ℂ) (N : A) (s : ℕ) (f : ℂ → ℂ) : A :=
  ∑ i ∈ range s, (iteratedDeriv i f β / (i.factorial : ℂ)) • N ^ i

end CompleteCrouzeix

namespace CompleteCrouzeix
open Module Set
open scoped DirectSum
variable {V : Type u_63} [AddCommGroup V] [Module ℂ V] [instFiniteDimensionalℂV : FiniteDimensional ℂ V]

noncomputable def primaryEquiv (T : Module.End ℂ V) :
    V ≃ₗ[ℂ] ⨁ β : ℂ, T.maxGenEigenspace β := by
  classical
  exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap T.maxGenEigenspace)
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      T.independent_maxGenEigenspace T.iSup_maxGenEigenspace_eq_top)).symm

noncomputable def primaryNilpotent (T : Module.End ℂ V) (β : ℂ) :
    Module.End ℂ (T.maxGenEigenspace β) :=
  (T - algebraMap ℂ (Module.End ℂ V) β).restrict
    (fun x hx => T.mapsTo_maxGenEigenspace_of_comm
      (Algebra.mul_sub_algebraMap_commutes T β) β (show x ∈ T.maxGenEigenspace β from hx))

noncomputable def primaryEval (T : Module.End ℂ V) (f : ℂ → ℂ) : Module.End ℂ V :=
  (primaryEquiv T).symm.toLinearMap ∘ₗ
    (DirectSum.lmap fun β => scalarJetEval β (primaryNilpotent T β) (finrank ℂ V) f) ∘ₗ
      (primaryEquiv T).toLinearMap

end CompleteCrouzeix

namespace CompleteCrouzeix
open Filter Topology Set Module
variable {n : Type u_67} [Fintype n] [DecidableEq n]

noncomputable def matrixAnalyticEval (A : Matrix n n ℂ) (f : ℂ → ℂ) : Matrix n n ℂ :=
  Matrix.toLinAlgEquiv'.symm (primaryEval (Matrix.toLinAlgEquiv' A) f)

end CompleteCrouzeix

namespace CompleteCrouzeix
open scoped ENNReal NNReal Matrix.Norms.L2Operator MatrixOrder Kronecker
variable {n : Type u_83} {m : Type u_84} [Fintype n] [DecidableEq n] [instFintypeM : Fintype m] [instDecidableEqM : DecidableEq m]

def completeAnalyticEval (D : Matrix n n ℂ) (F : ℂ → Matrix m m ℂ) :
    Matrix (n×m) (n×m) ℂ :=
  fun i j => matrixAnalyticEval D (fun z => F z i.2 j.2) i.1 j.1

end CompleteCrouzeix

namespace CompleteCrouzeix
open scoped Matrix MatrixOrder
variable {n : Type u_181} [Fintype n] [DecidableEq n] [Nonempty n]

def MetricFeasible (T : Matrix n n ℂ) (τ : ℝ) (H : Matrix n n ℂ) : Prop :=
  1 ≤ H ∧ H ≤ algebraMap ℝ (Matrix n n ℂ) τ ∧ Tᴴ * H * T ≤ H

end CompleteCrouzeix

end

noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Kronecker

namespace StructuralCrouzeix
open CompleteCrouzeix

def RegularAnalyticBoundaryAt (U : Set ℂ) (p : ℂ) : Prop :=
  ∃ χ : ℂ → ℂ, χ 0 = p ∧ AnalyticAt ℂ χ 0 ∧ deriv χ 0 ≠ 0 ∧
    (∀ᶠ z : ℂ in 𝓝 0, χ z ∈ frontier U ↔ z.im = 0)

structure IsAdmissible (U : Set ℂ) : Prop where
  isOpen : IsOpen U
  bounded : Bornology.IsBounded U
  convex : Convex ℝ U
  nonempty : U.Nonempty
  jordan : Nonempty (Circle ≃ₜ ↥(frontier U))
  regular : ∀ p ∈ frontier U, RegularAnalyticBoundaryAt U p

def IsMinimizing {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (τ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  MetricFeasible T τ H ∧
    ∀ (σ : ℝ) (J : Matrix (Fin n) (Fin n) ℂ),
      MetricFeasible T σ J → τ ≤ σ

def StrictlyFeasible {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ (τ : ℝ) (H : Matrix (Fin n) (Fin n) ℂ), H.IsHermitian ∧
    (H - 1).PosDef ∧
    (algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) τ - H).PosDef ∧
    (H - Tᴴ * H * T).PosDef

def analyticSupNorm {m : ℕ} (U : Set ℂ)
    (v : ℂ → Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  sSup ((fun z => ‖v z‖) '' closure U)

def boundaryPoint {U : Set ℂ} (G : ExteriorCoordinate U) (t : UnitAddCircle) : ℂ :=
  exteriorMap G.leading G.constant G.regular (t.toCircle : ℂ)

def FullEndpoint : Prop :=
  ∀ (U : Set ℂ), IsAdmissible U →
    (∀ a ∈ U, Nonempty (DiskCoordinate U a)) ∧
    Nonempty (ExteriorCoordinate U) ∧
    ∀ (a : ℂ), a ∈ U → ∀ (f : DiskCoordinate U a) (G : ExteriorCoordinate U),
      ∀ (n : ℕ), 0 < n → ∀ (A : Matrix (Fin n) (Fin n) ℂ),
        numericalRange A ⊆ U →
        let T := matrixAnalyticEval A f.toDisk
        StrictlyFeasible T ∧
        ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ 2 ∧
          (∃ H : Matrix (Fin n) (Fin n) ℂ, IsMinimizing T (κ ^ 2) H) ∧
          ∀ H : Matrix (Fin n) (Fin n) ℂ, IsMinimizing T (κ ^ 2) H →
            let S := CFC.sqrt H
            let A' := S * A * S⁻¹
            let D := S * T * S⁻¹
            H.PosDef ∧ IsUnit S ∧
            D = matrixAnalyticEval A' f.toDisk ∧
            Dᴴ * D ≤ 1 ∧ spectralRadius ℂ D < 1 ∧
            ‖S‖ * ‖S⁻¹‖ = κ ∧
            (∀ R : Matrix (Fin n) (Fin n) ℂ, IsUnit R →
              (R * T * R⁻¹)ᴴ * (R * T * R⁻¹) ≤ 1 →
              κ ≤ ‖R‖ * ‖R⁻¹‖) ∧
            ∃ Λ : C(UnitAddCircle, Matrix (Fin n) (Fin n) ℂ),
              (∀ t, (Λ t).PosSemidef) ∧
              (∫ t, Λ t ∂AddCircle.haarAddCircle) = 1 ∧
              ∀ (m : ℕ), 0 < m →
                ∀ v : ℂ → Matrix (Fin m) (Fin m) ℂ,
                  AnalyticOnNhd ℂ v (closure U) →
                  completeAnalyticEval A' v =
                    (∫ t, Λ t ⊗ₖ v (boundaryPoint G t) ∂AddCircle.haarAddCircle) ∧
                  ‖completeAnalyticEval A v‖ ≤ κ * analyticSupNorm U v

end StructuralCrouzeix
end

namespace StructuralCrouzeixReference

/-- Intrinsic structural representation and admissibility of the unit disk. -/
theorem challenge : StructuralCrouzeix.FullEndpoint ∧
    StructuralCrouzeix.IsAdmissible (Metric.ball (0 : ℂ) 1) := by
  sorry

end StructuralCrouzeixReference

end OAI
