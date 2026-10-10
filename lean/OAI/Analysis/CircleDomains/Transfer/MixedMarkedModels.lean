import OAI.Analysis.CircleDomains.Topology.MixedModelExhaustion
import OAI.Analysis.CircleDomains.Transfer.ShrinkingRealModels

namespace OAI

/-! Original marked ends in the common mixed model. These constructions
use the actual terminal fibers; no transport of dependent terminal types
from the real subfamily is necessary. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {S C : Type*} [LinearOrder C]
  {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ}
  {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
  {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}

namespace MixedModelExhaustion

variable (M : MixedModelExhaustion d data retained O ε ρ)

 def markIndex (n : ℕ) (s : S) : (M.stages n).indices :=
  ⟨(M.real.markIndex n s).val, by rw [M.same_indices n]; exact (M.real.markIndex n s).property⟩

 theorem eventually_markIndex (s : S) : ∀ᶠ n in atTop, (M.markIndex n s : S) = s :=
  M.real.eventually_markIndex s

 theorem core_model (n : ℕ) : M.real.cores n ⊆ openCompletedRegion (M.stages n).terminals.H := by
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact (M.stages n).core_model (infty_mem_sphericalCore (M.stages n).core)
  | coe z =>
    apply (M.stages n).core_model
    apply (coe_mem_sphericalCore _ _).mpr
    apply interior_subset ((M.stages n).core_contains ?_)
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈ M.real.cores n
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hp

 theorem eventually_sourceMark_captured (s : S) :
    ∀ᶠ n in atTop, d.sourceMark s ∈
      closedTerminalCap ((M.stages n).terminals.H (M.markIndex n s)) := by
  have hinf : OnePoint.infty ∈ G :=
    M.real.core_source 0 (M.real.plane_core 0 (Or.inr rfl))
  have hq : d.sourceMark s ≠ OnePoint.infty := by
    intro he
    exact d.sourceMark_outside s (he ▸ hinf)
  obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp hq
  filter_upwards [M.eventually_markIndex s] with n hn
  refine ⟨z, subset_closure ((M.stages n).terminals.fiber_subset (M.markIndex n s) ?_), hz⟩
  change π (z : Sphere) = σ (M.markIndex n s)
  rw [hn, hz]
  exact d.sourceMark_image s

 theorem eventually_marked_cap_subset (s : S) {W : Set Sphere}
    (hO : ∀ᶠ n in atTop, O n s ⊆ W) :
    ∀ᶠ n in atTop, closedTerminalCap ((M.stages n).terminals.H (M.markIndex n s)) ⊆ π ⁻¹' W := by
  filter_upwards [M.eventually_markIndex s, hO] with n hn hOn
  rintro p ⟨z, hz, rfl⟩
  have h := (M.stages n).terminals.closure_subset (M.markIndex n s) hz
  change π (z : Sphere) ∈ O n (M.markIndex n s) at h
  rw [hn] at h
  exact hOn h

end MixedModelExhaustion

 theorem MixedModelExhaustion.eventually_marked_cap_in_nhds
    {ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained (markedNeighborhoods σ) modelError ρ)
    (s : S) {W : Set Sphere} (hW : W ∈ 𝓝 (σ s)) :
    ∀ᶠ n in atTop, closedTerminalCap ((M.stages n).terminals.H (M.markIndex n s)) ⊆ π ⁻¹' W :=
  M.eventually_marked_cap_subset s (markedNeighborhoods_shrink σ s hW)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
