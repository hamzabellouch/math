import Mathlib
import OAI.Analysis.HardSphere.Density.DensityLinearity
import OAI.Analysis.HardSphere.Density.DensityBounds
import OAI.Analysis.HardSphere.Orbitals.OrbitalOperator

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere

attribute [local instance] groundScalarL2Complete

lemma mixedOccupation_lower {N : ℕ} (hN : 0<N) {L : Length} {a c : ℝ}
    (T : Density.Operator (ScalarL2 N L)) (hT : GroundSupported a T)
    (h : ∀u : Jet N L,IsGroundVector N L a u → c≤occupation hN u.1) :
    c ≤ mixedOccupation hN T := by
  apply T.compressionTrace_lower
  intro ψ hψ hn
  obtain ⟨u,hu,hg⟩ := hT ψ hψ hn
  rw [Orbital.norm_sq,←hu]
  exact h u hg

lemma mixedOccupation_le_one {N : ℕ} (hN : 0<N) {L : Length}
    (T : Density.Operator (ScalarL2 N L)) : mixedOccupation hN T≤1 := by
  apply T.compressionTrace_upper
  exact Orbital.map_norm_le hN

lemma mixedOccupation_pure {N : ℕ} (hN : 0<N) {L : Length}
    (ψ : ScalarL2 N L) (hψ : ‖ψ‖=1) :
    mixedOccupation hN (Density.pure ψ hψ)=occupation hN ψ := by
  rw [mixedOccupation,Density.pure_compression,Orbital.norm_sq]

lemma mixedOccupation_linear {N : ℕ} (hN : 0<N) {L : Length}
    (T U V : Density.Operator (ScalarL2 N L)) (c d : ℝ)
    (hV : V.toCLM=c • T.toCLM+d • U.toCLM) :
    mixedOccupation hN V=c*mixedOccupation hN T+d*mixedOccupation hN U :=
  T.compressionTrace_linear U V (Orbital.continuous hN) c d hV

theorem condensation_with_mixed :
    ∃ε₀ c₀ : ℝ,0<ε₀ ∧ 0<c₀ ∧
    ∀a ρ : ℝ,0<a → 0<ρ → ρ*a^3<ε₀ →
    ∀(N : ℕ→ℕ) (L : ℕ→Length) (hN : ∀k,0<N k),
      Tendsto N atTop atTop → Tendsto (fun k ↦ (L k).val) atTop atTop →
      Tendsto (fun k ↦ (N k:ℝ)/(L k).val^3) atTop (𝓝 ρ) →
      (∀Ψ : (k : ℕ)→Jet (N k) (L k),
        (∀k,IsGroundVector (N k) (L k) a (Ψ k)) →
        c₀≤liminf (fun k ↦ occupation (hN k) (Ψ k).1) atTop) ∧
      (∀T : (k : ℕ)→Density.Operator (ScalarL2 (N k) (L k)),
        (∀k,GroundSupported a (T k)) →
        c₀≤liminf (fun k ↦ mixedOccupation (hN k) (T k)) atTop) := by
  obtain ⟨ε,c,hε,hc,hevent⟩ := eventually_all_ground_occupation
  refine ⟨ε,c,hε,hc,?_⟩
  intro a ρ ha hρ hd N L hN hNtop hLtop hdensity
  have he := hevent a ρ ha hρ hd N L hN hNtop hLtop hdensity
  constructor
  · intro Ψ hΨ
    have hbounded : ∀ index, occupation (hN index) (Ψ index).1 ≤ (1 : ℝ) := by
      intro index
      simpa only [(hΨ index).2.2.1,one_pow] using
        occupation_le_norm_sq (hN index) (Ψ index).1
    apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop hbounded)
    filter_upwards [he] with index hindex
    exact hindex (Ψ index) (hΨ index)
  · intro T hT
    apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (x:=1) (fun k ↦ mixedOccupation_le_one (hN k) (T k)))
    filter_upwards [he] with k hk
    exact mixedOccupation_lower (hN k) (T k) (hT k) hk

end HardSphere
end
end

end OAI
