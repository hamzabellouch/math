import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceConfigurationRoles
import OAI.NumberTheory.Ostmann.Characters.UniformFinite

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Construction Preliminaries
open scoped BigOperators

def configurationCells {k Q : ℕ} (E : Finset (PrimeUpTo Q))
    (cfg : SourceConfiguration k) : Fin (configCellCount cfg) → Finset (PrimeUpTo Q) :=
  fun i => boundedRawLogCell E (configCellIndices cfg i)

@[simp] theorem mem_configurationCells {k Q : ℕ} (E : Finset (PrimeUpTo Q))
    (cfg : SourceConfiguration k) (i : Fin (configCellCount cfg)) (p : PrimeUpTo Q) :
    p ∈ configurationCells E cfg i ↔ p ∈ E ∧
      (configCellIndices cfg i : ℝ) ≤ Real.log p.val ∧
      Real.log p.val < (configCellIndices cfg i : ℝ)+1 := by
  simp only [configurationCells, boundedRawLogCell, Finset.mem_filter]

theorem configurationCells_subset {k Q : ℕ} (E : Finset (PrimeUpTo Q))
    (cfg : SourceConfiguration k) (i : Fin (configCellCount cfg)) :
    configurationCells E cfg i ⊆ E := Finset.filter_subset _ _

theorem configCellIndices_mem {k : ℕ} (cfg : SourceConfiguration k) (I : Finset ℤ)
    (ha : ∀ a, cfg.1 a ∈ I) (hl : ∀ j, ∀ a ∈ cfg.2 j, a ∈ I) :
    ∀ i, configCellIndices cfg i ∈ I :=
  configCellIndices_property cfg (fun a => a ∈ I) ha hl

theorem configurationCells_mass_lower {k Q : ℕ} (E : Finset (PrimeUpTo Q))
    (cfg : SourceConfiguration k) (I : Finset ℤ) (μ : ℝ)
    (ha : ∀ a, cfg.1 a ∈ I) (hl : ∀ j, ∀ a ∈ cfg.2 j, a ∈ I)
    (hI : ∀ a ∈ I, μ ≤ primeShellMass (boundedRawLogCell E a)) :
    ∀ i, μ ≤ primeShellMass (configurationCells E cfg i) := by
  intro i
  exact hI _ (configCellIndices_mem cfg I ha hl i)

theorem configurationCells_mass_pos {k Q : ℕ} (E : Finset (PrimeUpTo Q))
    (cfg : SourceConfiguration k) (I : Finset ℤ) (μ : ℝ) (hμ : 0 < μ)
    (ha : ∀ a, cfg.1 a ∈ I) (hl : ∀ j, ∀ a ∈ cfg.2 j, a ∈ I)
    (hI : ∀ a ∈ I, μ ≤ primeShellMass (boundedRawLogCell E a)) :
    ∀ i, 0 < primeShellMass (configurationCells E cfg i) :=
  fun i => hμ.trans_le (configurationCells_mass_lower E cfg I μ ha hl hI i)

theorem configurationCells_good {k Q : ℕ} (E : Finset (PrimeUpTo Q))
    (cfg : SourceConfiguration k) (f : PrimeUpTo Q → ℂ) (δ : ℝ)
    (ha : ∀ a, ∃ hm : 0 < primeShellMass (boundedRawLogCell E (cfg.1 a)),
      δ ≤ ((primeShellPrior (boundedRawLogCell E (cfg.1 a)) hm).cmean f).re)
    (hl : ∀ j, ∀ a ∈ cfg.2 j, ∃ hm : 0 < primeShellMass (boundedRawLogCell E a),
      δ ≤ ((primeShellPrior (boundedRawLogCell E a) hm).cmean f).re) :
    ∃ hm : ∀ i, 0 < primeShellMass (configurationCells E cfg i),
      ∀ i, δ ≤ ((primeShellPrior (configurationCells E cfg i) (hm i)).cmean f).re := by
  have h := configCellIndices_property cfg (fun a =>
    ∃ hm : 0 < primeShellMass (boundedRawLogCell E a),
      δ ≤ ((primeShellPrior (boundedRawLogCell E a) hm).cmean f).re) ha hl
  exact ⟨fun i => (h i).choose, fun i => (h i).choose_spec⟩

theorem configurationCells_good_of_mem {k Q : ℕ} (E : Finset (PrimeUpTo Q))
    (cfg : SourceConfiguration k) (I : Finset ℤ) (f : PrimeUpTo Q → ℂ) (δ : ℝ)
    (ha : ∀ a, cfg.1 a ∈ I) (hl : ∀ j, ∀ a ∈ cfg.2 j, a ∈ I)
    (hI : ∀ a ∈ I, ∃ hm : 0 < primeShellMass (boundedRawLogCell E a),
      δ ≤ ((primeShellPrior (boundedRawLogCell E a) hm).cmean f).re) :
    ∃ hm : ∀ i, 0 < primeShellMass (configurationCells E cfg i),
      ∀ i, δ ≤ ((primeShellPrior (configurationCells E cfg i) (hm i)).cmean f).re :=
  configurationCells_good E cfg f δ (fun a => hI _ (ha a)) (fun j a hj => hI a (hl j a hj))

theorem configurationCells_good_of_raw {k Q : ℕ} (E : Finset (PrimeUpTo Q))
    (cfg : SourceConfiguration k) (I : Finset ℤ) (f : PrimeUpTo Q → ℂ) (δ : ℝ)
    (ha : ∀ a, cfg.1 a ∈ I) (hl : ∀ j, ∀ a ∈ cfg.2 j, a ∈ I)
    (hI : ∀ a ∈ I, 0 < primeShellMass (boundedRawLogCell E a) ∧
      δ ≤ (∑ p ∈ boundedRawLogCell E a, (p.val : ℝ)⁻¹ * (f p).re) /
        primeShellMass (boundedRawLogCell E a)) :
    ∃ hm : ∀ i, 0 < primeShellMass (configurationCells E cfg i),
      ∀ i, δ ≤ ((primeShellPrior (configurationCells E cfg i) (hm i)).cmean f).re := by
  apply configurationCells_good_of_mem E cfg I f δ ha hl
  intro a hmem
  refine ⟨(hI a hmem).1, ?_⟩
  rw [prior_cmean_re, primeShellPrior_real_mean]
  exact (hI a hmem).2

end Ostmann.Characters.HigherBiasSource

end

end OAI
