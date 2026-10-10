import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowLocalDomain
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowGlobalExistence

namespace OAI

/-! Compact extensions of the autonomous field along a compact trajectory.
The extension has a complete C⁴ flow by bounded Picard existence. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal
namespace ContinuumCoulomb

theorem flow_c4_compact_extension {f : FlowPhase → FlowPhase} {S K : Set FlowPhase}
    (hS : IsOpen S) (hf : ContDiffOn ℝ 4 f S) (hK : IsCompact K) (hKS : K ⊆ S) :
    ∃ (g : FlowPhase → FlowPhase) (O : Set FlowPhase),
      ContDiff ℝ 4 g ∧ HasCompactSupport g ∧ IsOpen O ∧ K ⊆ O ∧ O ⊆ S ∧ EqOn g f O := by
  obtain ⟨R,_hR,hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : FlowPhase)
  obtain ⟨V,hV,hKV,hVS⟩ := hK.exists_isOpen_closure_subset
    ((hS.inter Metric.isOpen_ball).mem_nhdsSet.mpr (subset_inter hKS hKR))
  obtain ⟨O,hO,hKO,hOV⟩ := hK.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hKV)
  obtain ⟨b,hb,_hb01,hbs,hb1⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (4:ℕ∞)) hV isClosed_closure hOV
  have hbS : tsupport b ⊆ S := by
    rw [tsupport,hbs]
    exact hVS.trans inter_subset_left
  have hbc : HasCompactSupport b := by
    apply (isCompact_closedBall (0:FlowPhase) R).of_isClosed_subset isClosed_closure
    change closure (Function.support b) ⊆ Metric.closedBall (0:FlowPhase) R
    rw [hbs]
    exact hVS.trans (inter_subset_right.trans Metric.ball_subset_closedBall)
  let g : FlowPhase → FlowPhase := fun x => b x • f x
  refine ⟨g,O,?_,hbc.smul_right,hO,hKO,?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · exact hb.contDiffAt.smul (hf.contDiffAt (hS.mem_nhds (hbS hx)))
    · have heq : g =ᶠ[𝓝 x] 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        change b y • f y = 0
        simp only [hy,Pi.zero_apply,zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · exact subset_closure.trans (hOV.trans (subset_closure.trans (hVS.trans inter_subset_left)))
  · intro x hx
    change b x • f x = f x
    rw [(hb1 x).mp (subset_closure hx),one_smul]

theorem flow_compact_global_exists {f : FlowPhase → FlowPhase}
    (hf : ContDiff ℝ 4 f) (hc : HasCompactSupport f) :
    ∃ G : FlowPhase → ℝ → FlowPhase,
      (∀ x, G x 0 = x) ∧ (∀ x t, HasDerivAt (G x) (f (G x t)) t) ∧
      ContDiff ℝ 4 (fun z : ℝ × FlowPhase => G z.2 z.1) := by
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hf (by norm_num)
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hf.continuous
  let B' : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  obtain ⟨G,h0,hG⟩ := flow_bounded_global_exists hL
    (B := B') (fun x => (hB x).trans (le_max_left _ _))
  exact ⟨G,h0,hG,flow_global_joint_C4 hf hL G h0 hG⟩

end ContinuumCoulomb

end

end OAI
