import OAI.NumberTheory.EgyptianFractions.RandomResidueRealization
import OAI.NumberTheory.EgyptianFractions.GeometricRandomRanges

namespace OAI
noncomputable section
open Filter
open scoped BigOperators

namespace Problem337.RandomProducts
open GeometricRandomRanges

/-- The middle-level small-residue and every-terminal-numerator guarantees
hold for one common family of actual labelled prime samples. The onset is
uniform in the prime pool and no Fourier hypothesis remains. -/
theorem eventually_common_geometric_random_residues (D : ℝ) (hD : 1 ≤ D) :
    ∀ᶠ S : ℝ in atTop, ∀ P : Finset ℕ,
      (∀ p ∈ P, Nat.Prime p) →
      (∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101) →
      S ^ 99 ≤ (P.card : ℝ) →
      ∃ (f : Fin 1000 → ((Fin (blockLength S) × Bool) → P))
        (exceptional : ℕ → Finset ℕ),
        (∀ j ∈ middleTests D S, exceptional j ⊆ middleLevel D S j ∧
          ((exceptional j).card : ℝ) ≤
            cutoff D S j * Real.exp (-(blockLength S : ℝ) / 1000) ∧
          ∀ u ∈ middleLevel D S j, u ∉ exceptional j →
            (Real.exp (-(blockLength S : ℝ) / 10000) / 2) *
                (2 : ℝ) ^ blockLength S ≤
              ((Finset.univ.filter (fun I : Fin (blockLength S) → Bool =>
                (sampledRemainder (f 0) u I : ℝ) ≤ cutoff D S (j + 1))).card : ℝ)) ∧
        ∀ u ∈ terminalRange S, ∃ i : Fin 1000, ∃ I : Fin (blockLength S) → Bool,
          (sampledRemainder (f i) u I : ℝ) < (u : ℝ) ^ (9999 / 10000 : ℝ) := by
  classical
  obtain ⟨N, hN⟩ := exists_common_sampled_residue_realization
  filter_upwards [eventually_selectionRanges D hD (max N 1),
    ResidueLevels.eventually_scale_bounds,
    ResidueLevels.tendsto_scale.eventually
      (eventually_ge_atTop (10000 * Real.log 65536)),
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (Real.log 65536 / 10))]
    with S hr hscale hsmallm hlogsmall
  intro P hp hi hs
  have hSpos : 0 < S := by linarith [hr.parameter_large]
  have hlogpos : 0 < Real.log S := by linarith [hscale.1]
  have hmS : (blockLength S : ℝ) ≤ S := by
    have hratio : S / Real.log S ≤ S := by
      apply (div_le_iff₀ hlogpos).mpr
      nlinarith [hscale.1]
    exact hscale.2.2.2.trans hratio
  have hsmallV : 10000 * Real.log 65536 ≤ 100000 * Real.log S := by
    linarith
  obtain ⟨f, exceptional, hmiddle, hterminal⟩ :=
    hN S P ℕ (middleTests D S) (middleLevel D S) (cutoff D S) (terminalRange S)
      (by linarith [hr.parameter_large]) hp hi hs hr.scale_large hsmallm
      hr.tests_card hr.cutoff_positive hr.level_card
      (fun j hj u hu => ⟨(mem_middleLevel hu).1, (mem_middleLevel hu).2.2,
        hr.middle_window j hj u hu⟩)
      (fun u hu => ⟨hr.terminal_threshold u hu, (hr.terminal_window u hu).1,
        le_min (hr.terminal_window u hu).2 ((hr.terminal_window u hu).2.trans hmS),
        hsmallV.trans (hr.terminal_window u hu).1⟩)
  refine ⟨f, exceptional, ?_, hterminal⟩
  intro j hj
  obtain ⟨hsub, hcard, hcount⟩ := hmiddle j hj
  refine ⟨hsub, hcard, ?_⟩
  intro u hu hnot
  have hstep : cutoff D S (j + 1) =
      Real.exp (-(blockLength S : ℝ) / 10000) * cutoff D S j := by
    unfold cutoff
    rw [ResidueLevels.level_succ]
    congr 2
    dsimp [blockLength, ResidueLevels.scale]
    ring
  simpa only [hstep] using hcount u hu hnot
/-- The middle-level small-residue and every-terminal-numerator guarantees
hold for one common family of actual labelled prime samples. The onset is
uniform in the prime pool and no Fourier hypothesis remains. -/
theorem eventually_common_geometric_random_fractional_residues (D : ℝ) (hD : 1 ≤ D) :
    ∀ᶠ S : ℝ in atTop, ∀ P : Finset ℕ,
      (∀ p ∈ P, Nat.Prime p) →
      (∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101) →
      S ^ 99 ≤ (P.card : ℝ) →
      ∃ (f : Fin 1000 → ((Fin (blockLength S) × Bool) → P))
        (exceptional : ℕ → Finset ℕ),
        (∀ j ∈ middleTests D S, exceptional j ⊆ middleLevel D S j ∧
          ((exceptional j).card : ℝ) ≤
            cutoff D S j * Real.exp (-(blockLength S : ℝ) / 1000) ∧
          ∀ u ∈ middleLevel D S j, u ∉ exceptional j →
            (Real.exp (-(blockLength S : ℝ) / 10000) / 2) *
                (2 : ℝ) ^ blockLength S ≤
              ((Finset.univ.filter (fun I : Fin (blockLength S) → Bool =>
                Int.fract (-(sampledProduct (f 0) I : ℝ) / u) <
                  Real.exp (-(blockLength S : ℝ) / 10000))).card : ℝ)) ∧
        ∀ u ∈ terminalRange S, ∃ i : Fin 1000, ∃ I : Fin (blockLength S) → Bool,
          (sampledRemainder (f i) u I : ℝ) < (u : ℝ) ^ (9999 / 10000 : ℝ) := by
  classical
  obtain ⟨N, hN⟩ := exists_common_sampled_residue_realization_strict
  filter_upwards [eventually_selectionRanges D hD (max N 1),
    ResidueLevels.eventually_scale_bounds,
    ResidueLevels.tendsto_scale.eventually
      (eventually_ge_atTop (10000 * Real.log 65536)),
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (Real.log 65536 / 10))]
    with S hr hscale hsmallm hlogsmall
  intro P hp hi hs
  have hSpos : 0 < S := by linarith [hr.parameter_large]
  have hlogpos : 0 < Real.log S := by linarith [hscale.1]
  have hmS : (blockLength S : ℝ) ≤ S := by
    have hratio : S / Real.log S ≤ S := by
      apply (div_le_iff₀ hlogpos).mpr
      nlinarith [hscale.1]
    exact hscale.2.2.2.trans hratio
  have hsmallV : 10000 * Real.log 65536 ≤ 100000 * Real.log S := by
    linarith
  obtain ⟨f, exceptional, hmiddle, hterminal⟩ :=
    hN S P ℕ (middleTests D S) (middleLevel D S) (cutoff D S) (terminalRange S)
      (by linarith [hr.parameter_large]) hp hi hs hr.scale_large hsmallm
      hr.tests_card hr.cutoff_positive hr.level_card
      (fun j hj u hu => ⟨(mem_middleLevel hu).1, (mem_middleLevel hu).2.2,
        hr.middle_window j hj u hu⟩)
      (fun u hu => ⟨hr.terminal_threshold u hu, (hr.terminal_window u hu).1,
        le_min (hr.terminal_window u hu).2 ((hr.terminal_window u hu).2.trans hmS),
        hsmallV.trans (hr.terminal_window u hu).1⟩)
  refine ⟨f, exceptional, ?_, hterminal⟩
  intro j hj
  obtain ⟨hsub, hcard, hcount⟩ := hmiddle j hj
  refine ⟨hsub, hcard, ?_⟩
  intro u hu hnot
  simpa only [sampledRemainder_lt_iff_fract (f 0) u (mem_middleLevel hu).1] using
    hcount u hu hnot

end Problem337.RandomProducts

end

end OAI
