import OAI.MeasureTheory.Falconer.Fourier.SpatialFourierIntegration
import OAI.MeasureTheory.Falconer.Estimates.DistanceFormFubini
import OAI.MeasureTheory.Falconer.Fourier.InheritedSymbolMeasurability

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ComplexConjugate

noncomputable def spatialPhasedSymbol (s : ℝ) (ξ : Plane)
    (b : Plane → UnitCircle → ℂ) (x : Plane) (ω : UnitCircle) : ℂ :=
  spatialFourierPhase s ξ x * b x ω

theorem spatialPhasedSymbol_norm (s : ℝ) (ξ : Plane)
    (b : Plane → UnitCircle → ℂ) (x : Plane) (ω : UnitCircle) :
    ‖spatialPhasedSymbol s ξ b x ω‖ = ‖b x ω‖ := by
  simp [spatialPhasedSymbol, spatialFourierPhase_norm]

theorem spatialPhasedSymbol_measurable (s : ℝ) (ξ : Plane)
    (b : Plane → UnitCircle → ℂ)
    (hb : Measurable (fun z : Plane × UnitCircle => b z.1 z.2)) :
    Measurable (fun z : Plane × UnitCircle => spatialPhasedSymbol s ξ b z.1 z.2) := by
  apply Measurable.mul _ hb
  unfold spatialFourierPhase
  fun_prop

theorem spatialPhasedSymbol_joint_measurable (s : ℝ)
    (b : Plane → UnitCircle → ℂ)
    (hb : Measurable (fun z : Plane × UnitCircle => b z.1 z.2)) :
    Measurable (fun p : Plane × (Plane × UnitCircle) =>
      spatialPhasedSymbol s p.1 b p.2.1 p.2.2) := by
  apply Measurable.mul _ (hb.comp measurable_snd)
  unfold spatialFourierPhase
  fun_prop

theorem spatialPhased_inherited {ι : Type*} (S : Finset ι) (d : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ) (s : ℝ) (ξ x : Plane) (ω : UnitCircle) :
    spatialPhasedSymbol s ξ (inheritedCircleSymbol S d k Q ρ m N lam sig J i h) x ω =
      inheritedCircleSymbol S d k Q ρ m N lam sig J i
        (fun x => spatialFourierPhase s ξ x * h x) x ω := by
  simp only [spatialPhasedSymbol, inheritedCircleSymbol, mul_assoc]

theorem sourceDistanceKernel_phased (s : ℝ) (ξ : Plane) (ψ : UnitCircle → ℂ)
    (b₁ b₂ : Plane → UnitCircle → ℂ) (r : ℝ) (x y : Plane) :
    sourceDistanceKernel ψ (spatialPhasedSymbol s ξ b₁) (spatialPhasedSymbol s ξ b₂) r x y =
      spatialPairPhase s ξ (x,y) * sourceDistanceKernel ψ b₁ b₂ r x y := by
  simp only [sourceDistanceKernel, spatialPhasedSymbol, spatialPairPhase, map_mul,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  ring

end PlanarFalconer

end OAI
