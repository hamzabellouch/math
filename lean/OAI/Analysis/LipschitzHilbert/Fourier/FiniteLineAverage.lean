import OAI.Analysis.LipschitzHilbert.Trees.FiniteLineGrid
import OAI.Analysis.LipschitzHilbert.Estimates.NestedPerturbation

namespace OAI

/-! Products of the actual finer-cell step factors on a finite line grid. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

private theorem nonnegative_fiber_profile {α κ : Type*}
    (P : α → κ) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hconstant : ∀ x y, P x = P y → f x = f y) :
    ∃ c : κ → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ x, f x = c (P x) := by
  classical
  let c := fun i => if h : ∃ x, P x = i then f h.choose else 0
  refine ⟨c, ?_, ?_⟩
  · intro i
    dsimp only [c]
    split_ifs with h
    · exact hf _
    · exact le_rfl
  · intro x
    have h : ∃ y, P y = P x := ⟨x, rfl⟩
    dsimp only [c]
    rw [dite_eq_left h]
    exact hconstant x h.choose h.choose_spec.symm

namespace FiniteLineGrid

/-- The actual finer-cell factors have a finite profile, so their product
is integrable on every finite measure. -/
theorem integrable_product (g : FiniteLineGrid) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (Γ : ℕ → ℝ → ℝ)
    (hΓ : ∀ n < g.depth, ∀ x, 0 ≤ Γ n x)
    (hconstant : ∀ n < g.depth, ∀ x y,
      g.index (n + 1) x = g.index (n + 1) y → Γ n x = Γ n y) :
    Integrable (fun x => ∏ n ∈ Finset.range g.depth, Γ n x) μ := by
  classical
  have hprofile : ∀ n : ℕ, ∃ c : Fin (g.branching ^ g.depth) → ℝ,
      (∀ i, 0 ≤ c i) ∧ ∀ x, (if n < g.depth then Γ n x else 1) = c (g.index (n + 1) x) := by
    intro n
    apply nonnegative_fiber_profile
    · intro x
      split_ifs with hn
      · exact hΓ n hn x
      · exact zero_le_one
    · intro x y hxy
      split_ifs with hn
      · exact hconstant n hn x y hxy
      · rfl
  choose c _ hfactor using hprofile
  have hint := integrable_nested_product μ g.index (fun _ => g.parent) c g.depth
    (g.measurable_index_fiber g.depth)
    (fun n hn x => g.index_parent hn x)
  have heq : (fun x => ∏ n ∈ Finset.range g.depth, Γ n x) =
      (fun x => ∏ n ∈ Finset.range g.depth, c n (g.index (n + 1) x)) := by
    funext x
    apply Finset.prod_congr rfl
    intro n hn
    simpa only [ite_eq_left (Finset.mem_range.mp hn)] using hfactor n x
  rwa [heq]

/-- Finer-cell constancy and current-cell averages suffice for the actual
line-grid product. The finite profiles are constructed from the step factors;
the partition refinement is the proved floor-grid identity. -/
theorem average_product_le (g : FiniteLineGrid) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (Γ : ℕ → ℝ → ℝ)
    (hΓ : ∀ n < g.depth, ∀ x, 0 ≤ Γ n x)
    (hconstant : ∀ n < g.depth, ∀ x y,
      g.index (n + 1) x = g.index (n + 1) y → Γ n x = Γ n y)
    (haverage : ∀ n < g.depth, ∀ i : Fin (g.branching ^ g.depth),
      (∫ x in {x | g.index n x = i}, Γ n x ∂μ) ≤
        μ.real {x | g.index n x = i}) :
    (∫ x, ∏ n ∈ Finset.range g.depth, Γ n x ∂μ) ≤ μ.real Set.univ := by
  classical
  have hprofile : ∀ n : ℕ, ∃ c : Fin (g.branching ^ g.depth) → ℝ,
      (∀ i, 0 ≤ c i) ∧ ∀ x, (if n < g.depth then Γ n x else 1) = c (g.index (n + 1) x) := by
    intro n
    apply nonnegative_fiber_profile
    · intro x
      split_ifs with hn
      · exact hΓ n hn x
      · exact zero_le_one
    · intro x y hxy
      split_ifs with hn
      · exact hconstant n hn x y hxy
      · rfl
  choose c hc hfactor using hprofile
  have hav := nested_average_product_le μ g.index (fun _ => g.parent) c g.depth
    (fun n _ => g.measurable_index_fiber n)
    (fun n hn x => g.index_parent hn x) (fun n _ => hc n)
    (fun n hn i => by simpa only [← hfactor n, ite_eq_left hn] using haverage n hn i)
  have heq : (fun x => ∏ n ∈ Finset.range g.depth, Γ n x) =
      (fun x => ∏ n ∈ Finset.range g.depth, c n (g.index (n + 1) x)) := by
    funext x
    apply Finset.prod_congr rfl
    intro n hn
    simpa only [ite_eq_left (Finset.mem_range.mp hn)] using hfactor n x
  rw [heq]
  exact hav

end FiniteLineGrid
end LipschitzHilbert

end

end OAI
