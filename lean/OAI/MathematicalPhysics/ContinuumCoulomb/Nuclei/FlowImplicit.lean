import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.PublishedFlowInput
import OAI.Analysis.BiholderTransport.Calculus.PathCalculus
import OAI.Analysis.BiholderTransport.Calculus.ImplicitNeighborhood
import OAI.Analysis.BiholderTransport.Regularity.UnitTime

namespace OAI

/-! The finite C⁴ implicit-function step for the actual four-dimensional
autonomous lift of the three-dimensional time-dependent flow. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb

abbrev FlowPhase := ℝ × Position
abbrev FlowPath := C(WeakMTWTransport.UnitTime,FlowPhase)

theorem flow_c4_implicit_neighborhood
    (F : (ℝ × FlowPhase) × FlowPath → FlowPath) (hF : ContDiff ℝ 4 F)
    (a : ℝ × FlowPhase) (b : FlowPath)
    (hi : (fderiv ℝ F (a,b) ∘L inr ℝ (ℝ × FlowPhase) FlowPath).IsInvertible) :
    ∃ U : (ℝ × FlowPhase) → FlowPath, ∃ S : Set (ℝ × FlowPhase),
      IsOpen S ∧ a ∈ S ∧ ContDiffOn ℝ 4 U S ∧ U a = b ∧
        ∀ x ∈ S, F (x,U x) = F (a,b) := by
  let U := hF.contDiffAt.implicitFunction (by norm_num) hi
  have hU : ContDiffAt ℝ 4 U a := hF.contDiffAt.contDiffAt_implicitFunction (by norm_num) hi
  have hb : U a = b := hF.contDiffAt.implicitFunction_apply_self (by norm_num) hi
  have hc : ∀ᶠ x in 𝓝 a, ContDiffAt ℝ 1 U x :=
    (hU.of_le (by norm_num : (1:ℕ∞ω) ≤ 4)).eventually (by simp)
  have hid : Continuous (fun p => fderiv ℝ F p ∘L inr ℝ (ℝ × FlowPhase) FlowPath) :=
    (hF.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hin : ∀ᶠ p in 𝓝 (a,b),
      (fderiv ℝ F p ∘L inr ℝ (ℝ × FlowPhase) FlowPath).IsInvertible :=
    hid.continuousAt (WeakMTWTransport.isOpen_invertible_endomorphism.mem_nhds hi)
  have hgraph : ContinuousAt (fun x => (x,U x)) a := continuousAt_id.prodMk hU.continuousAt
  have hgi : ∀ᶠ x in 𝓝 a,
      (fderiv ℝ F (x,U x) ∘L inr ℝ (ℝ × FlowPhase) FlowPath).IsInvertible :=
    hgraph (by simpa only [hb] using! hin)
  have heq : ∀ᶠ x in 𝓝 a, F (x,U x) = F (a,b) :=
    hF.contDiffAt.eventually_apply_implicitFunction (by norm_num) hi
  obtain ⟨V,hVsub,hV,hbase⟩ := mem_nhds_iff.mp
    (hF.contDiffAt.eventually_apply_eq_iff_implicitFunction (by norm_num) hi)
  have hgin : ∀ᶠ x in 𝓝 a, (x,U x) ∈ V :=
    hgraph (by simpa only [hb] using! hV.mem_nhds hbase)
  obtain ⟨S,hSsub,hS,ha⟩ := mem_nhds_iff.mp (hc.and (hgi.and (heq.and hgin)))
  refine ⟨U,S,hS,ha,?_,hb,fun x hx => (hSsub hx).2.2.1⟩
  intro x hx
  have hh := hSsub hx
  let W := hF.contDiffAt.implicitFunction (by norm_num) hh.2.1
  have hW : ContDiffAt ℝ 4 W x := hF.contDiffAt.contDiffAt_implicitFunction (by norm_num) hh.2.1
  have hwx : W x = U x := hF.contDiffAt.implicitFunction_apply_self (by norm_num) hh.2.1
  have hWgraph : ContinuousAt (fun z => (z,W z)) x := continuousAt_id.prodMk hW.continuousAt
  have hWV : ∀ᶠ z in 𝓝 x, (z,W z) ∈ V :=
    hWgraph (by simpa only [hwx] using hV.mem_nhds hh.2.2.2)
  have hev : U =ᶠ[𝓝 x] W := by
    filter_upwards [hWV,hF.contDiffAt.eventually_apply_implicitFunction (by norm_num) hh.2.1]
      with z hz hz'
    exact (hVsub hz).mp (hz'.trans hh.2.2.1)
  exact (hW.congr_of_eventuallyEq hev).contDiffWithinAt

end ContinuumCoulomb

end

end OAI
