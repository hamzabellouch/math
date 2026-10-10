import OAI.NumberTheory.Ostmann.Construction.SelectedTailCells
import OAI.NumberTheory.Ostmann.Arithmetic.MovingProtectedTarget

namespace OAI

/-! # Actual top and compensation cell lists -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def selectedTailCellPrimes (A B : Set ℕ) (N : ℕ) (X : ℝ)
    (hi : ℕ) (D : Finset ℕ) (j : ℕ) : Finset ℕ :=
  (primeLogCellSet 1 0 j ((j : ℝ) + 1) \
    tailCellExceptionalPrimes A B N (summandTailCutoff X) hi (tailCollisionCutoff X)) \ D

def SelectedSmallTailCell (A B : Set ℕ) (N : ℕ) (a C L X : ℝ)
    (hi : ℕ) (D : Finset ℕ) (target : ℝ) (j : ℕ) : Prop :=
  target ≤ j ∧ (j : ℝ) ≤ target + 64 * tailDefectBudget a C X + 1 ∧
    (j : ℝ) + 1 ≤ Real.exp ((11 / 1000 : ℝ) * L) ∧
    let Q := selectedTailCellPrimes A B N X hi D j
    Real.exp (-(2 * L)) ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) ∧
    0 < (∑ p ∈ Q, (p : ℝ)⁻¹) ∧
    (∑ p ∈ Q, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 * L) ∧
    (∀ p ∈ Q, p.Prime ∧ Real.exp (j : ℝ) < p ∧
      (p : ℝ) ≤ Real.exp ((j : ℝ) + 1) ∧
      (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
      ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3)

theorem EventuallyPrimeSumset.selected_compensation_cells_at
    (P0 : PublishedProgressionInput) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C : ℝ) (hM : MertensLowerBound C) :
    ∃ a : ℝ, 0 < a ∧ ∀ (k : ℕ), 0 < k →
      ∀ BD Bz : ℝ, 0 ≤ BD → 0 ≤ Bz →
      ∀ᶠ L : ℝ in atTop, ∀ X : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ X → X ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp X →
      ∀ J cb : ℝ, 16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
      J ≤ 32 * Real.exp ((1 / 100 : ℝ) * L) → 0 ≤ cb → cb ≤ J / 4 →
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      ∃ (top : ℕ) (centers : List ℕ),
        SelectedSmallTailCell A B N a C L X hi D ((J - cb) / 6) top ∧
        List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j)
          centers (movingCompensationTargets J (movingCompensationGaps k BD Bz L)) := by
  obtain ⟨a, ha, hcells⟩ := h.selected_tail_cells_at P0 hsize hA hB N hN C hM
  refine ⟨a, ha, ?_⟩
  intro k hk BD Bz hBD hBz
  filter_upwards [hcells, eventual_protected_cell_target_range,
    eventual_prescribed_compensation_range k hk BD Bz hBD hBz]
    with L hcells htop hcomp
  intro X hXlo hXhi hi hhi J cb hJlo hJhi hcb0 hcb D hD
  have hchoose (target : ℝ) (hlo : Real.exp ((1 / 100 : ℝ) * L) ≤ target)
      (hupper : target ≤ Real.exp ((105 / 10000 : ℝ) * L)) :
      ∃ j, SelectedSmallTailCell A B N a C L X hi D target j :=
    hcells X hXlo hXhi hi hhi target hlo hupper D hD
  obtain ⟨htlo, hthi⟩ := htop J cb hJlo hJhi hcb0 hcb
  obtain ⟨top, htop⟩ := hchoose ((J - cb) / 6) htlo hthi
  have hex : ∀ w ∈ movingCompensationTargets J (movingCompensationGaps k BD Bz L),
      ∃ j, SelectedSmallTailCell A B N a C L X hi D (w / 4) j := by
    intro w hw
    obtain ⟨hlo, hupper⟩ := hcomp J hJlo hJhi w hw
    exact hchoose (w / 4) hlo hupper
  have hlist (ws : List ℝ)
      (hw : ∀ w ∈ ws, ∃ j, SelectedSmallTailCell A B N a C L X hi D (w / 4) j) :
      ∃ cs : List ℕ, List.Forall₂
        (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs ws := by
    induction ws with
    | nil => exact ⟨[], .nil⟩
    | cons w ws ih =>
      obtain ⟨j, hj⟩ := hw w (by simp)
      obtain ⟨cs, hcs⟩ := ih (fun x hx => hw x (by simp [hx]))
      exact ⟨j :: cs, .cons hj hcs⟩
  obtain ⟨centers, hcenters⟩ := hlist _ hex
  exact ⟨top, centers, htop, hcenters⟩

theorem EventuallyPrimeSumset.selected_compensation_cells
    (P0 : PublishedProgressionInput) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (C : ℝ) (hM : MertensLowerBound C) :
    ∃ N : ℕ, ∃ a : ℝ, 0 < a ∧ ∀ (k : ℕ), 0 < k →
      ∀ BD Bz : ℝ, 0 ≤ BD → 0 ≤ Bz →
      ∀ᶠ L : ℝ in atTop, ∀ X : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ X → X ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp X →
      ∀ J cb : ℝ, 16 * Real.exp ((1 / 100 : ℝ) * L) ≤ J →
      J ≤ 32 * Real.exp ((1 / 100 : ℝ) * L) → 0 ≤ cb → cb ≤ J / 4 →
      ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      ∃ (top : ℕ) (centers : List ℕ),
        SelectedSmallTailCell A B N a C L X hi D ((J - cb) / 6) top ∧
        List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j)
          centers (movingCompensationTargets J (movingCompensationGaps k BD Bz L)) := by
  obtain ⟨N, hN⟩ := h.disjoint_tail_residues
  obtain ⟨a, ha, hrest⟩ := h.selected_compensation_cells_at P0 hsize hA hB N hN C hM
  exact ⟨N, a, ha, hrest⟩

end Ostmann

end OAI
