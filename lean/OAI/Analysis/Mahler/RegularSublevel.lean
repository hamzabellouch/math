import OAI.Analysis.Mahler.RegularLevelCharts
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.OrderClosed

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes

def regularSublevel {d : ℕ} (U : Set (Fin d → ℝ)) (g : (Fin d → ℝ) → ℝ) (R : ℝ) :=
  U ∩ {x | g x < R}

lemma isOpen_regularSublevel {d : ℕ} {U : Set (Fin d → ℝ)} {g : (Fin d → ℝ) → ℝ}
    {R : ℝ} (hU : IsOpen U) (hg : ContinuousOn g U) : IsOpen (regularSublevel U g R) := by
  exact hg.isOpen_inter_preimage hU isOpen_Iio

/-- Regularity forces a point on the level to be approached from below:
otherwise it would be a local minimum with zero derivative. -/
theorem level_mem_closure_sublevel {d : ℕ} {U : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} {R : ℝ} {x : Fin d → ℝ}
    (hU : IsOpen U) (hx : x ∈ U) (heq : g x = R) (hreg : fderiv ℝ g x ≠ 0) :
    x ∈ closure (regularSublevel U g R) := by
  by_contra hc
  have hm : IsLocalMin g x := by
    filter_upwards [hU.mem_nhds hx, isClosed_closure.isOpen_compl.mem_nhds hc] with y hy hyn
    rw [heq]
    by_contra! hn
    exact hyn (subset_closure ⟨hy, hn⟩)
  exact hreg hm.fderiv_eq_zero

/-- The boundary of the actual relatively defined sublevel is exactly the
regular level, provided its closure stays inside U. -/
theorem frontier_regularSublevel {d : ℕ} {U : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} {R : ℝ} (hU : IsOpen U) (hg : ContinuousOn g U)
    (hcl : closure (regularSublevel U g R) ⊆ U)
    (hreg : ∀ x ∈ U, g x = R → fderiv ℝ g x ≠ 0) :
    frontier (regularSublevel U g R) = U ∩ {x | g x = R} := by
  have ho := isOpen_regularSublevel (R := R) hU hg
  rw [ho.frontier_eq]
  ext x
  constructor
  · rintro ⟨hx, hnot⟩
    have hxU := hcl hx
    refine ⟨hxU, le_antisymm ?_ ?_⟩
    · by_contra! hlt
      have hn : ∀ᶠ y in 𝓝 x, R < g y :=
        (hg.continuousAt (hU.mem_nhds hxU)).preimage_mem_nhds (isOpen_Ioi.mem_nhds hlt)
      obtain ⟨y, hy, hys⟩ := mem_closure_iff_nhds.mp hx {y | R < g y} hn
      exact (not_lt_of_ge (le_of_lt (show R < g y from hy))) (show g y < R from hys.2)
    · exact le_of_not_gt (fun h => hnot ⟨hxU, h⟩)
  · rintro ⟨hxU, heq⟩
    exact ⟨level_mem_closure_sublevel hU hxU heq (hreg x hxU heq),
      fun h => (ne_of_lt h.2) heq⟩

 theorem isCompact_regularLevel {d : ℕ} {U : Set (Fin d → ℝ)}
    {g : (Fin d → ℝ) → ℝ} {R : ℝ} (hU : IsOpen U) (hg : ContinuousOn g U)
    (hc : IsCompact (closure (regularSublevel U g R)))
    (hcl : closure (regularSublevel U g R) ⊆ U)
    (hreg : ∀ x ∈ U, g x = R → fderiv ℝ g x ≠ 0) :
    IsCompact (U ∩ {x | g x = R}) := by
  rw [← frontier_regularSublevel hU hg hcl hreg]
  exact hc.of_isClosed_subset isClosed_frontier frontier_subset_closure

end MahlerStokes

end

end OAI
