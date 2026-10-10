import OAI.NumberTheory.Jacobsthal.Probability.SourceCompactCoupling
import OAI.NumberTheory.Jacobsthal.Renewal.FlaggedOccupationBound

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualFlaggedCompact

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling
open PrimeCompactVisits FlaggedOccupationBound PersistentFailureFlag ActualFlagInvariant

variable {w ell S : ℝ} {start : Node}

noncomputable def compactVisit (K : ℝ) (z : JointState w ell S start) : ℝ≥0∞ :=
  ENNReal.ofReal (visit K z.1)

noncomputable def compactPotential (K : ℝ) (z : JointState w ell S start) : ℝ≥0∞ :=
  ENNReal.ofReal (potential K z.1)

theorem compactVisit_measurable (K : ℝ) : Measurable (compactVisit (w:=w) (ell:=ell) (S:=S) (start:=start) K) :=
  (measurable_of_countable (fun p : ChainState w ell S start => ENNReal.ofReal (visit K p))).comp measurable_fst

theorem compactPotential_measurable (K : ℝ) : Measurable (compactPotential (w:=w) (ell:=ell) (S:=S) (start:=start) K) :=
  (measurable_of_countable (fun p : ChainState w ell S start => ENNReal.ofReal (potential K p))).comp measurable_fst

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem joint_compact_drift {K : ℝ} (hK : 0 ≤ K) (v mesh : ℝ) (z : JointState w ell S start) :
    compactVisit K z+(∫⁻ y,compactPotential K y ∂jointKernel hw hell hS0 hS hr hs hsS v mesh z) ≤
      compactPotential K z := by
  have hmeas : Measurable (fun p : ChainState w ell S start => ENNReal.ofReal (potential K p)) := measurable_of_countable _
  have heq : (∫⁻ y,compactPotential K y ∂jointKernel hw hell hS0 hS hr hs hsS v mesh z) =
      ∫⁻ p,ENNReal.ofReal (potential K p) ∂chain w ell S start z.1 := by
    rw [← jointKernel_left hw hell hS0 hS hr hs hsS v mesh z.1 z.2,
      lintegral_map hmeas measurable_fst]
    rfl
  rw [heq]
  exact actual_row_drift hw hell hS0 hS hr hs hsS hK z.1

include hw hell hS0 hS hr hsS in

theorem actual_flagged_compact_visits {K : ℝ} (hK : 0 ≤ K) (mesh : ℝ) (N : ℕ) :
    (∑ n ∈ range N, ∫⁻ z,selected (compactVisit K) z ∂CouplingData.sourceLaw w ell S start hs mesh n) ≤
      ENNReal.ofReal (K+1)*CouplingData.sourceLaw w ell S start hs mesh N failed := by
  have hbound : ∀ z : JointState w ell S start,compactPotential K z ≤ ENNReal.ofReal (K+1) :=
    fun z => ENNReal.ofReal_le_ofReal (potential_le hK z.1)
  have h := finite_selected_occupation
    (jointKernel hw hell hS0 hS hr hs hsS (Real.log start.gap) mesh)
    (mismatch_measurable mesh) (compactVisit_measurable K) (compactPotential_measurable K)
    ENNReal.ofReal_ne_top hbound
    (joint_compact_drift hw hell hS0 hS hr hs hsS hK (Real.log start.gap) mesh)
    (FlaggedSourceStart.sourceJoint w ell S start hs) N
  exact h

end NumberTheoryLean.ActualFlaggedCompact

end

end Erdos970

end OAI
