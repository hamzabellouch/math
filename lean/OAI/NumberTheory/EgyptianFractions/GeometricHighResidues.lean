import OAI.NumberTheory.EgyptianFractions.DeterministicSubsetResidues
import OAI.NumberTheory.EgyptianFractions.GeometricRawDensity

namespace OAI
noncomputable section
open Filter
open scoped BigOperators

namespace Problem337.GeometricDensity

/-- The open lower cutoff of a geometric level is precisely the natural
interval required by deterministic residue localization. -/
theorem mem_high_residue_interval {DM S : ℝ} {j u : ℕ}
    (hu : u ∈ Finset.Icc 1 ⌊cutoff DM (1 / 10000) S j⌋₊)
    (hnext : cutoff DM (1 / 10000) S (j + 1) < (u : ℝ)) :
    u ∈ Finset.Icc
      (⌊Real.exp (-(ResidueLevels.scale S : ℝ) / 10000) *
        cutoff DM (1 / 10000) S j⌋₊ + 1)
      ⌊cutoff DM (1 / 10000) S j⌋₊ := by
  have heq : cutoff DM (1 / 10000) S (j + 1) =
      Real.exp (-(ResidueLevels.scale S : ℝ) / 10000) *
        cutoff DM (1 / 10000) S j := by
    rw [cutoff, ResidueLevels.level_succ]
    congr 1
    congr 1
    ring
  rw [heq] at hnext
  refine Finset.mem_Icc.mpr ⟨?_, (Finset.mem_Icc.mp hu).2⟩
  have hpos : 0 ≤ Real.exp (-(ResidueLevels.scale S : ℝ) / 10000) *
      cutoff DM (1 / 10000) S j :=
    mul_nonneg (Real.exp_pos _).le (ResidueLevels.level_pos _ _ _ _).le
  exact Nat.succ_le_iff.mpr ((Nat.floor_lt hpos).mpr hnext)

/-- The actual deterministic block supplies all high geometric levels at one
common onset, with a single exceptional-set function. No Fourier estimate or
cutoff-window hypothesis is left to the final arithmetic assembly. -/
theorem eventually_high_geometric_subset_residues
    (DM : ℝ) (hDM : 255 ≤ 4 * (DM + 2)) :
    ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
      ∀ p : Fin (ResidueLevels.scale S) → ℕ,
        (∀ i, (p i).Prime) → Function.Injective p →
        (∀ i, (p i : ℝ) ≤ S ^ (101 : ℕ)) →
        ∃ E : ℕ → Finset ℕ, ∀ j : ℕ,
          Real.exp S < cutoff DM (1 / 10000) S j →
          ((E j).card : ℝ) ≤ cutoff DM (1 / 10000) S j *
              Real.exp (-(ResidueLevels.scale S : ℝ) / 1000) ∧
          ∀ u ∈ Finset.Icc 1 ⌊cutoff DM (1 / 10000) S j⌋₊,
            u ∉ E j → cutoff DM (1 / 10000) S (j + 1) < (u : ℝ) →
            contraction (1 / 10000) S * (2 : ℝ) ^ ResidueLevels.scale S / 2 ≤
              ((Finset.univ.filter (fun I : Fin (ResidueLevels.scale S) → Fin 2 =>
                Int.fract (-((C * ResidueConstruction.subsetEntry p I : ℕ) : ℝ) / u) <
                  contraction (1 / 10000) S)).card : ℝ) := by
  classical
  filter_upwards [eventually_deterministic_subset_residues (4 * (DM + 2)) hDM,
    ResidueLevels.eventually_scale_bounds] with S hdist hscale
  intro C hClo hChi p hp hinj hsize
  have hrho : contraction (1 / 10000) S =
      Real.exp (-(ResidueLevels.scale S : ℝ) / 10000) := by
    unfold contraction
    congr 1
    ring
  have hlevel (j : ℕ) : cutoff DM (1 / 10000) S j ≤
      Real.exp ((4 * (DM + 2)) * S / 4) := by
    apply Real.exp_le_exp.mpr
    have hn : 0 ≤ (1 / 10000 : ℝ) * (ResidueLevels.scale S : ℝ) * j := by
      positivity
    change (DM + 2) * S - (1 / 10000 : ℝ) * ResidueLevels.scale S * j ≤ _
    nlinarith
  have hex : ∀ j : ℕ, ∃ E : Finset ℕ,
      Real.exp S < cutoff DM (1 / 10000) S j →
      (E.card : ℝ) ≤ cutoff DM (1 / 10000) S j *
          Real.exp (-(ResidueLevels.scale S : ℝ) / 1000) ∧
      ∀ u ∈ Finset.Icc 1 ⌊cutoff DM (1 / 10000) S j⌋₊,
        u ∉ E → cutoff DM (1 / 10000) S (j + 1) < (u : ℝ) →
        contraction (1 / 10000) S * (2 : ℝ) ^ ResidueLevels.scale S / 2 ≤
          ((Finset.univ.filter (fun I : Fin (ResidueLevels.scale S) → Fin 2 =>
            Int.fract (-((C * ResidueConstruction.subsetEntry p I : ℕ) : ℝ) / u) <
              contraction (1 / 10000) S)).card : ℝ) := by
    intro j
    by_cases hj : Real.exp S < cutoff DM (1 / 10000) S j
    · obtain ⟨E, _, hcard, hcount⟩ := hdist (ResidueLevels.scale S)
        (cutoff DM (1 / 10000) S j) C hscale.2.2.1 hscale.2.2.2
        hj.le (hlevel j) hClo hChi p hp hinj hsize
      refine ⟨E, fun _ => ⟨hcard, ?_⟩⟩
      intro u hu hnot hnext
      rw [hrho]
      exact hcount u (mem_high_residue_interval hu hnext) hnot
    · exact ⟨∅, fun h => False.elim (hj h)⟩
  choose E hE using hex
  exact ⟨E, hE⟩

end Problem337.GeometricDensity

end

end OAI
