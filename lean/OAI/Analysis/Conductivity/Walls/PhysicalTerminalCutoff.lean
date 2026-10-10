import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalOpenVoltage
import OAI.Analysis.Conductivity.Sobolev.OriginalSmoothMultiplier

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory
namespace PhysicalFiniteEndingData

def terminalCore (η : ℝ) : Set Coord3 :=
  {y | η≤terminalTime 0 y ∧ ∀ k : Fin 2,terminalTime k.succ y≤-η}

lemma terminalCore_closed (η : ℝ) : IsClosed (terminalCore η) := by
  simp only [terminalCore,ofPred_and,ofPred_forall]
  exact (isClosed_le continuous_const (terminalTime_locallyLipschitz 0).continuous).inter
    (isClosed_iInter (fun k => isClosed_le (terminalTime_locallyLipschitz k.succ).continuous continuous_const))

lemma terminalCore_subset {η : ℝ} (hη : 0≤η) : terminalCore η⊆physicalBlockRegion := by
  intro y hy
  rw [physicalBlockRegion_time_iff]
  exact ⟨hη.trans hy.1,fun k => (hy.2 k).trans (by linarith)⟩

lemma terminalCore_compact {η : ℝ} (hη : 0≤η) : IsCompact (terminalCore η) :=
  physicalBlockRegion_compact.of_isClosed_subset (terminalCore_closed η) (terminalCore_subset hη)

lemma terminalCore_subset_open {η : ℝ} (hη : 0<η) : terminalCore η⊆physicalOpenBlock := by
  intro y hy
  change WithLp.toLp 2 y∈sourceOpenBlock
  rw [sourceOpenBlock_time_iff]
  exact ⟨hη.trans_le hy.1,fun k => (hy.2 k).trans_lt (by linarith)⟩

lemma terminalCore_subset_interior {α β : ℝ} (hab : α<β) :
    terminalCore β⊆interior (terminalCore α) := by
  intro y hy
  apply mem_interior_iff_mem_nhds.mpr
  have hp : ∀ᶠ x in 𝓝 y,α<terminalTime 0 x :=
    (terminalTime_locallyLipschitz 0).continuous.continuousAt.eventually
      (lt_mem_nhds (hab.trans_le hy.1))
  have hc (k : Fin 2) : ∀ᶠ x in 𝓝 y,terminalTime k.succ x< -α :=
    (terminalTime_locallyLipschitz k.succ).continuous.continuousAt.eventually
      (gt_mem_nhds ((hy.2 k).trans_lt (by linarith)))
  filter_upwards [hp,eventually_all.mpr hc] with x hp hc
  exact ⟨hp.le,fun k => (hc k).le⟩

lemma terminal_cutoff_exists {η : ℝ} (hη : 0<η) :
    ∃ χ : Coord3 → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) χ ∧ HasCompactSupport χ ∧
      tsupport χ⊆physicalOpenBlock ∧ (∀ y∈terminalCore η,χ y=1) := by
  have hs := terminalCore_compact (show 0≤η/2 by positivity)
  obtain ⟨χ,hχ1,hχ0,hχb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ Coord3) (terminalCore_closed η)
    (terminalCore_subset_interior (show η/2<η by linarith)) (n:=↑(⊤:ℕ∞))
  have hts : tsupport (χ : Coord3 → ℝ)⊆terminalCore (η/2) := by
    apply closure_minimal _ hs.isClosed
    intro x hx
    by_contra hn
    exact hx (hχ0 x hn)
  refine ⟨χ,χ.contMDiff.contDiff,HasCompactSupport.intro hs hχ0,
    hts.trans (terminalCore_subset_open (by positivity)),?_⟩
  intro y hy
  have hh : (χ : Coord3 → ℝ)=ᶠ[𝓝 y] (fun _ => 1) := hχ1.filter_mono (nhds_le_nhdsSet hy)
  exact hh.eq_of_nhds

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
