import Mathlib
import OAI.Analysis.HardSphere.FormDomain.AeSelfGradientSquare
import OAI.Analysis.HardSphere.FormDomain.AeGradientPhase
import OAI.Analysis.HardSphere.Conditioning.LintegralReferenceMeasure
import OAI.Analysis.HardSphere.Bridges.AccessibleAuxiliary
import OAI.Analysis.HardSphere.PathBounds.RegularVisitors
import OAI.Analysis.HardSphere.Collisions.InsertionProducer
import OAI.Analysis.HardSphere.Kernels.KernelPi
import OAI.Analysis.HardSphere.Kernels.ParametricTrial
import OAI.Analysis.HardSphere.PathBounds.UniformVisitMGF
import OAI.Analysis.HardSphere.Density.GroundProjection

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere

theorem condensation_all_ground_states :
    ∃ε₀ c₀ : ℝ,0<ε₀ ∧ 0<c₀ ∧
    ∀(a ρ : ℝ) (ha : 0<a),0<ρ → ρ*a^3<ε₀ →
    ∀(N : ℕ→ℕ) (L : ℕ→Length) (hN : ∀k,0<N k),
      Tendsto N atTop atTop → Tendsto (fun k ↦ (L k).val) atTop atTop →
      Tendsto (fun k ↦ (N k:ℝ)/(L k).val^3) atTop (𝓝 ρ) →
      (∀Ψ : (k : ℕ)→Jet (N k) (L k),
        (∀k,IsGroundVector (N k) (L k) a (Ψ k)) →
        c₀≤liminf (fun k ↦ occupation (hN k) (Ψ k).1) atTop) ∧
      (∀T : (k : ℕ)→Density.Operator (ScalarL2 (N k) (L k)),
        (∀k,GroundSupported a (T k)) →
        c₀≤liminf (fun k ↦ mixedOccupation (hN k) (T k)) atTop) ∧
      (∀hG : ∀k,groundSpace (N k) (L k) a≠⊥,
        c₀≤liminf (fun k ↦ mixedOccupation (hN k)
          (normalizedGroundProjection (N k) (L k) a ha (hG k))) atTop) := by
  obtain ⟨ε,c,hε,hc,h⟩ := condensation_with_mixed
  refine ⟨ε,c,hε,hc,?_⟩
  intro a ρ ha hρ hd N L hN hNtop hLtop hdensity
  obtain ⟨hp,hm⟩ := h a ρ ha hρ hd N L hN hNtop hLtop hdensity
  refine ⟨hp,hm,?_⟩
  intro hG
  exact hm (fun k ↦ normalizedGroundProjection (N k) (L k) a ha (hG k))
    (fun k ↦ normalizedGroundProjection_supported (N k) (L k) a ha (hG k))

end HardSphere
end
end

end OAI
