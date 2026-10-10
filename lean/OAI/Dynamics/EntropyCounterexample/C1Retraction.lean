import OAI.Dynamics.EntropyCounterexample.C1Coordinates

namespace OAI

noncomputable section

namespace Problem340

namespace HasLocalC1Extension

theorem contDiffOn_comp {X D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {e : X → E} {f : X → F} (hf : HasLocalC1Extension e f)
    (r : D → X) {V : Set D} (hV : IsOpen V)
    (hr : ContDiffOn ℝ 1 (e ∘ r) V) :
    ContDiffOn ℝ 1 (f ∘ r) V := by
  intro y hy
  obtain ⟨U, hU, hryU, F, hF, hcomm⟩ := hf (r y)
  have hrAt : ContDiffAt ℝ 1 (e ∘ r) y := hr.contDiffAt (hV.mem_nhds hy)
  have hFAt : ContDiffAt ℝ 1 F (e (r y)) := hF.contDiffAt (hU.mem_nhds hryU)
  have hcomp : ContDiffAt ℝ 1 (F ∘ e ∘ r) y := hFAt.comp y hrAt
  apply ContDiffAt.contDiffWithinAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hrAt.continuousAt.preimage_mem_nhds (hU.mem_nhds hryU)] with z hz
  exact hcomm (r z) hz

theorem exists_fderiv_bound_on_compact {X D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {e : X → E} {f : X → F} (hf : HasLocalC1Extension e f)
    (r : D → X) {V K : Set D} (hV : IsOpen V)
    (hr : ContDiffOn ℝ 1 (e ∘ r) V)
    (hK : IsCompact K) (hKV : K ⊆ V) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ y ∈ K, ‖fderiv ℝ (f ∘ r) y‖ ≤ B := by
  have hcont := (hf.contDiffOn_comp r hV hr).continuousOn_fderiv_of_isOpen hV le_rfl
  obtain ⟨B, hB⟩ := hK.bddAbove_image (hcont.norm.mono hKV)
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro y hy
  exact (hB (Set.mem_image_of_mem _ hy)).trans (le_max_right _ _)

end HasLocalC1Extension

end Problem340

end

end OAI
