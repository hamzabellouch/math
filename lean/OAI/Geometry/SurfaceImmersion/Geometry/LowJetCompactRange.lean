import OAI.Geometry.SurfaceImmersion.Geometry.LowJetPrefixBounds

namespace OAI

/-! One compact positional-jet range for all maps in a bounded C2 family. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem bounded_lowJet_range {U : Set Base} (hU : IsOpen U)
    (K : Compacts Base) (hUK : U ⊆ K) {C : ℝ} (hC : 0 ≤ C) :
    ∃ Q : Set LowJet, IsCompact Q ∧ ∀ (G : Base → Space), ContDiff ℝ ∞ G →
      WeightedBound U 1 2 C G → MapsTo (lowJet G) U Q := by
  obtain ⟨D,_,hd⟩ := bounded_lowJet_prefix hU K hUK 0
  refine ⟨Metric.closedBall 0 (D+C),isCompact_closedBall _ _,?_⟩
  intro G hG hb p hp
  have hj := hd G hG 1 C zero_lt_one le_rfl hC (fun j hj => by
    simpa only [one_pow,div_one] using hb.mono_order (by omega : j ≤ 2))
  simpa only [Metric.mem_closedBall,dist_zero_right] using hj.norm_le hp

end ClosedSurfaceR4.JetPolynomial

end

end OAI
