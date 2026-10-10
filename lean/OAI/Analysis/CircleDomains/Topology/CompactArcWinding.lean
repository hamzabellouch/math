import OAI.Analysis.CircleDomains.Modulus.NormalizedArgument
import OAI.Analysis.CircleDomains.Topology.CirclePathPrefixes

namespace OAI

/-! Uniform winding bounds for initial portions of a compact simple-arc
family, in any continuous angular coordinate on the punctured plane. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

open FiniteTransfer

def initialArcAngles {b : ℂ}
    (q : C({x : ℂ // x ≠ b}, UnitAddCircle))
    (γ : C(PathTime, ℂ)) (hi : Injective γ) (he : γ ⊤ = b)
    (c : PathTime) (hc : c < ⊤) : C(unitInterval, UnitAddCircle) :=
  ⟨fun t => q ⟨γ (t * c), fun h => by
    have ht : t * c = ⊤ := hi (h.trans he.symm)
    exact (not_le_of_gt hc) (ht ▸ unitInterval.mul_le_right)⟩,
    q.continuous.comp (((γ.continuous.comp (continuous_id.mul continuous_const))).subtype_mk _)⟩

theorem compact_initial_arc_lifts_bounded
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (b : ℂ)
    (hinj : ∀ γ ∈ K, Injective γ) (hend : ∀ γ ∈ K, γ ⊤ = b)
    (q : C({x : ℂ // x ≠ b}, UnitAddCircle)) (c : PathTime) (hc : c < ⊤) :
    ∃ M : ℝ, ∀ γ : K, ∀ t : unitInterval,
      |realCirclePathLift (initialArcAngles q γ.val (hinj _ γ.property)
        (hend _ γ.property) c hc) t| ≤ M := by
  let F : K → C(unitInterval, UnitAddCircle) := fun γ =>
    initialArcAngles q γ.val (hinj _ γ.property) (hend _ γ.property) c hc
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply q.continuous.comp
    apply Continuous.subtype_mk
    exact continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_snd.mul continuous_const))
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨M, hM⟩ := compact_circle_path_lifts_bounded (range F) (isCompact_range hF)
  exact ⟨M, fun γ t => hM (F γ) (mem_range_self γ) t⟩

end CircleDomainRigidity

end

end OAI
