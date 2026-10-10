import OAI.MeasureTheory.DyadicAvoidance.GridStabilityFin
import OAI.MeasureTheory.DyadicAvoidance.FiniteTableModel
import OAI.MeasureTheory.DyadicAvoidance.WindowData

namespace OAI

noncomputable section
namespace Problem310

open FiniteTableModel

/-- Actual selector stability for arbitrary canonical window data. The gap is
chosen before the window recursion and all its resolutions. Prefix and sibling
gap fields of `W` may be applied directly to the displayed strict cutoff. -/
theorem exists_windowData_selector_stability (M d : ℕ) (p : ℝ) (hp : 0 < p) :
    ∃ g : ℕ, 2 ≤ g ∧ ∀ r₀ : ℕ, ∀ W : WindowData (M + 1) d g r₀,
      ∃ G : Set ℝ, MeasurableSet G ∧
        (∀ x : ℝ, x + 1 ∈ G ↔ x ∈ G) ∧
        MeasureTheory.volume (Gᶜ ∩ Set.Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p ∧
        ∀ x ∈ G, ∀ P : Node M d, ∀ i : Fin M, ∀ n : ℕ,
          W.b (P.val ++ [i.castSucc]) + g < n →
          ∀ t ∈ Set.Icc (1 : ℝ) 2,
          ∀ ω : SelectorTable (fun P : Node M d => fun i : Fin M =>
            W.b (P.val ++ [i.castSucc])),
          selectorValue (fun P : Node M d => fun i : Fin M =>
            W.b (P.val ++ [i.castSucc])) ω P.val i (x + t * ((2 : ℝ)⁻¹) ^ n) =
          selectorValue (fun P : Node M d => fun i : Fin M =>
            W.b (P.val ++ [i.castSucc])) ω P.val i x := by
  obtain ⟨g, hg, hgeometry⟩ :=
    exists_uniform_grid_stability (ι := Node M d × Fin M) p hp
  refine ⟨g, hg, fun r₀ W ↦ ?_⟩
  let bS : Node M d → Fin M → ℕ := fun P i => W.b (P.val ++ [i.castSucc])
  obtain ⟨G, hGm, hGp, hGbudget, hGkey⟩ := hgeometry (fun e => bS e.1 e.2)
  refine ⟨G, hGm, hGp, hGbudget, ?_⟩
  intro x hx P i n hn t ht ω
  have hk := hGkey x hx (P, i) n (by dsimp [bS]; omega) t ht
  have ha : selectorAddress bS P i (x + t * ((2 : ℝ)⁻¹) ^ n) =
      selectorAddress bS P i x := by
    unfold selectorAddress
    rw [hk]
  change selectorValue bS ω P.val i (x + t * ((2 : ℝ)⁻¹) ^ n) =
    selectorValue bS ω P.val i x
  rw [selectorValue_valid, selectorValue_valid, ha]

end Problem310

end

end OAI
