import OAI.Analysis.LipschitzHilbert.Phase.AngularCountBridge

namespace OAI

/-! The unshrunk path child costs at most one additional retained cell. -/

noncomputable section

open Set

namespace LipschitzHilbert.AngularGrid

theorem independent_cells_card_le_one_exception {ι : Type*} [DecidableEq ι]
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox) (d : ι → ℝ)
    (z : ℝ × ℝ) (cutoff : ℝ) (base level : ℕ) (parent : ℤ)
    (cells : Finset ℤ) (exception : ℤ) {rho B K D : ℝ}
    (hprecision : cutoff / (g.branching : ℝ) ^ level ≤ rho / B ^ 2)
    (hspan : g.width base ≤ B * rho)
    (hancestor : ∀ c ∈ cells,
      g.cellTops tops (fun i => (T i).slope) d cutoff level c ⊆
        g.cellTops tops (fun i => (T i).slope) d cutoff base parent)
    (hsignificant : ∀ c ∈ cells, c ≠ exception →
      ∃ i ∈ g.cellTops tops (fun i => (T i).slope) d cutoff level c, (T i).radius z ≤ K)
    (hindependent : (cells : Set ℤ).Pairwise (fun c e => ¬g.neighbors level rho c e))
    (hcount : ∀ I : Finset ι, I ⊆ tops →
      (∀ i ∈ I, (T i).radius z ≤ K) →
      (∀ i ∈ I, d i ≤ rho / B ^ 2) →
      (∀ i ∈ I, ∀ j ∈ I, |(T i).slope - (T j).slope| ≤ B * rho) →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope - (T j).slope|) →
      (I.card : ℝ) ≤ D) : (cells.card : ℝ) ≤ D + 1 := by
  classical
  have herase := g.independent_cells_card_le tops T d z cutoff base level parent
    (cells.erase exception) hprecision hspan
    (fun c hc => hancestor c (Finset.mem_of_mem_erase hc))
    (fun c hc => hsignificant c (Finset.mem_of_mem_erase hc)
      (Finset.ne_of_mem_erase hc))
    (hindependent.mono (by intro c hc; exact Finset.mem_of_mem_erase hc)) hcount
  by_cases he : exception ∈ cells
  · have hcard := Finset.card_erase_add_one he
    have hreal : (cells.card : ℝ) = ((cells.erase exception).card : ℝ) + 1 := by
      exact_mod_cast hcard.symm
    linarith
  · simpa only [Finset.erase_eq_of_notMem he] using herase.trans (by linarith : D ≤ D + 1)

end LipschitzHilbert.AngularGrid

end

end OAI
