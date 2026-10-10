import OAI.Geometry.SurfaceImmersion.Atlas.PhaseTransverseDefiner
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteCurveLocalDefiners

namespace OAI

/-! Finite boundary defining functions pulled through an actual nonlinear
phase chart. Crossings and phase tangencies are the only exceptions. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma finite_phase_curve_definers {ι : Type*} [Fintype ι]
    (C V : ι → Set Base) (ρ : ι → Base → ℝ)
    (hC : ∀ i, IsClosed (C i)) (hV : ∀ i, IsOpen (V i))
    (hCV : ∀ i, C i ⊆ V i) (hρ : ∀ i, ContDiffOn ℝ ∞ (ρ i) (V i))
    (hzero : ∀ i x, x ∈ C i → ρ i x = 0)
    {φ : Base → ℝ} {f : Base → Base} (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    {K P : Set Base} (hK : K ⊆ ⋃ i, f ⁻¹' C i)
    (hcross : ∀ i j, i ≠ j → (f ⁻¹' C i) ∩ (f ⁻¹' C j) ⊆ P)
    (hphase : ∀ p ∈ K \ P, φ ∘ f =ᶠ[𝓝 p] Prod.fst)
    (hD : ∀ p ∈ K \ P, coordDet (fderiv ℝ f p) ≠ 0)
    (htrans : ∀ i p, p ∈ K \ P → f p ∈ C i →
      covectorDet (phaseDerivative φ (f p)) (phaseDerivative (ρ i) (f p)) ≠ 0) :
    ∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
      ∃ g : Base → ℝ, ContDiffOn ℝ ∞ g N ∧ (∀ x ∈ K ∩ N, g x = 0) ∧
        fderiv ℝ g p dy ≠ 0 := by
  apply finite_curve_local_definers (fun i => f ⁻¹' C i) (fun i => f ⁻¹' V i)
    (fun i => ρ i ∘ f)
  · exact fun i => (hC i).preimage hf.continuous
  · exact fun i => (hV i).preimage hf.continuous
  · exact fun i x hx => hCV i hx
  · exact fun i => (hρ i).comp hf.contDiffOn (fun _ hx => hx)
  · exact fun i x hx => hzero i (f x) hx
  · exact hK
  · exact hcross
  · intro i p hp hi
    apply phase_chart_transverse_definer_at (hφ.differentiable (by simp) _)
      (((hρ i).contDiffAt ((hV i).mem_nhds (hCV i hi))).differentiableAt (by simp))
      (hf.differentiable (by simp) _) (hphase p hp) (hD p hp) (htrans i p hp hi)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
