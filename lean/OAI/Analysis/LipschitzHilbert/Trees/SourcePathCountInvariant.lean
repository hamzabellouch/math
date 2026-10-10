import OAI.Analysis.LipschitzHilbert.Trees.SourceStoppedAmplitude

namespace OAI

/-! A terminal path is independent of how far the finite hierarchy is
extended. Thus the individual terminal counts used by the plane theorem
can be replaced by one finite count for every top in a root. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem firstMassStop_eq_of_terminal (n : ℕ → ℝ) (M : ℝ) (c d : ℕ)
    (hc : n c ≤ M) (hd : n d ≤ M) :
    firstMassStop n c M = firstMassStop n d M := by
  have hs := firstMassStop_spec n c M hc
  have ht := firstMassStop_spec n d M hd
  apply le_antisymm
  · by_contra h
    have hlt := hs.2.2 (firstMassStop n d M) (Nat.lt_of_not_ge h)
    exact (not_lt_of_ge ht.2.1) hlt
  · by_contra h
    have hlt := ht.2.2 (firstMassStop n c M) (Nat.lt_of_not_ge h)
    exact (not_lt_of_ge hs.2.1) hlt

namespace AngularGrid
variable {τ σ X : Type*} {κ : Type} [Fintype κ]

theorem sourceActivePathValue_count_congr {Kb : ℕ}
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a alpha p M : ℝ) (hM : 0 ≤ M)
    (hKb : 0 < Kb) (shift : Fin Kb) (top : τ) (htop : top ∈ tops)
    (c d : ℕ)
    (hc : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint shift c))
    (hd : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint shift d)) (x : X) :
    g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
      phase a alpha p M shift top c x =
    g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
      phase a alpha p M shift top d x := by
  rw [g.source_active_path_eq_stopped_product tops slope precision cutoff weight hp hw
    K gap packets assigned stop value phase a alpha p M hM hKb shift top htop c hc x,
    g.source_active_path_eq_stopped_product tops slope precision cutoff weight hp hw
    K gap packets assigned stop value phase a alpha p M hM hKb shift top htop d hd x]
  congr 2
  apply firstMassStop_eq_of_terminal
  · rw [g.shiftedPathMass_terminal_zero tops slope precision cutoff weight shift top c hc x]
    exact hM
  · rw [g.shiftedPathMass_terminal_zero tops slope precision cutoff weight shift top d hd x]
    exact hM

/-- The maximum of the actual individual terminal counts is terminal
for every top in the finite root family. -/
theorem source_common_terminal {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (precision : τ → ℝ) (cutoff : ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hKb : 0 < Kb) (shift : Fin Kb) (count : τ → ℕ)
    (hterminal : ∀ t ∈ tops, ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint shift (count t))) :
    ∀ t ∈ tops, ¬g.eligible cutoff (precision t)
      (ShiftedBlocks.endpoint shift (tops.sup count)) := by
  intro t ht he
  have hle : ShiftedBlocks.endpoint shift (count t) ≤
      ShiftedBlocks.endpoint shift (tops.sup count) :=
    (ShiftedBlocks.endpoint_strictMono hKb shift).monotone (Finset.le_sup ht)
  exact hterminal t ht (g.eligible_of_le (hp t ht) hle he)

end AngularGrid
end LipschitzHilbert

end

end OAI
