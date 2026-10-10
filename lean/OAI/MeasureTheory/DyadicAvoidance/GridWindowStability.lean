import OAI.MeasureTheory.DyadicAvoidance.GridStabilityFin
import OAI.MeasureTheory.DyadicAvoidance.WindowPlacement

namespace OAI

noncomputable section
namespace Problem310

/-- Uniform stability for a finite sequence of windows. The gap is selected
before any window lengths are fixed. -/
theorem exists_window_stability (K : ℕ) (p : ℝ) (hp : 0 < p) :
    ∃ g : ℕ, 2 ≤ g ∧ ∀ len : ℕ → ℕ, ∃ G : Set ℝ,
      MeasurableSet G ∧ (∀ x : ℝ, x + 1 ∈ G ↔ x ∈ G) ∧
      MeasureTheory.volume (Gᶜ ∩ Set.Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p ∧
      ∀ x ∈ G, ∀ f e : ℕ, f < e → e < K →
        ∀ n ∈ WindowPlacement.window len g e, ∀ t ∈ Set.Icc (1 : ℝ) 2,
          GridSeparation.dyadicKey (WindowPlacement.finish len g f)
            (x + t * ((2 : ℝ)⁻¹) ^ n) =
          GridSeparation.dyadicKey (WindowPlacement.finish len g f) x := by
  obtain ⟨g, hg, hstable⟩ := exists_uniform_grid_stability (ι := Fin K) p hp
  refine ⟨g, hg, fun len ↦ ?_⟩
  obtain ⟨G, hGm, hGp, hGbudget, hGkey⟩ :=
    hstable (fun i : Fin K ↦ WindowPlacement.finish len g i.val)
  refine ⟨G, hGm, hGp, hGbudget, ?_⟩
  intro x hx f e hfe heK n hn t ht
  have hfK : f < K := hfe.trans heK
  apply hGkey x hx ⟨f, hfK⟩ n ?_ t ht
  have hgap := WindowPlacement.gap_of_lt len g hfe
  have hstart := (WindowPlacement.mem_window.mp hn).1
  dsimp
  omega

end Problem310

end

end OAI
