import OAI.Analysis.NumericalRange.Model
import OAI.Analysis.NumericalRange.ConvexBarrier
import OAI.Analysis.NumericalRange.BoundaryNormals
import OAI.Analysis.NumericalRange.DiskCalculus
import OAI.Analysis.NumericalRange.CompleteResolvent
import OAI.Analysis.NumericalRange.MetricFeasibility

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
open Set MeasureTheory
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

end OAI
