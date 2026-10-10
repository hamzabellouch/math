import OAI.NumberTheory.Ostmann.Characters.HigherCharacterDecorrelation
import OAI.NumberTheory.Ostmann.QuadraticCenter.HarmonicQuadraticSmallness
import OAI.NumberTheory.Ostmann.Characters.TailCharacterBias

namespace OAI

/-! # Combining quadratic and higher-order translated decorrelation -/
namespace Ostmann
open Filter
open scoped Classical BigOperators Topology

noncomputable def tailCharacterBias (A : Set ℕ) (N p : ℕ) : ℝ :=
  maximalQuadraticBias (tailSupport A N p) p + higherCharacterBias A N p

noncomputable def tailCharacterBandMass (A : Set ℕ) (N : ℕ) (α β L : ℝ) : ℝ :=
  ∑ p ∈ closedLogLogPrimeBand α β L, (p : ℝ)⁻¹ * tailCharacterBias A N p

theorem closedLogLogPrimeBand_eq_iterated (α β L : ℝ) :
    closedLogLogPrimeBand α β L = iteratedLogPrimeBand α β L := by
  ext p
  rw [mem_closedLogLogPrimeBand_iff, mem_iteratedLogPrimeBand_iff]

theorem tailCharacterBandMass_eq (A : Set ℕ) (N : ℕ) (α β L : ℝ) :
    tailCharacterBandMass A N α β L =
      harmonicQuadraticBandMass A N α β L + higherCharacterBandMass A N α β L := by
  simp only [tailCharacterBandMass, tailCharacterBias, mul_add, Finset.sum_add_distrib,
    harmonicQuadraticBandMass, harmonicQuadraticBias, higherCharacterBandMass,
    ← closedLogLogPrimeBand_eq_iterated, div_eq_mul_inv, mul_comm]

theorem tailCharacterBias_nonneg (A : Set ℕ) (N p : ℕ) : 0 ≤ tailCharacterBias A N p :=
  add_nonneg (maximalQuadraticBias_nonneg _ _) (higherCharacterBias_nonneg _ _ _)

theorem PublishedProgressionInput.all_character_decorrelation
    (P0 : PublishedProgressionInput)
    (hsize : PublishedSummandSizeBound) {CM : ℝ} (hM : MertensEstimate CM)
    {Aset Bset : Set ℕ} (hAset : Aset.Infinite) (hBset : Bset.Infinite)
    (hsum : EventuallyPrimeSumset Aset Bset) (N₀ : ℕ)
    (hN₀ : ∀ p, p.Prime → Disjoint (tailResidues Aset N₀ p) (negTailResidues Bset N₀ p))
    (hquad : (fun T => closedQuadraticBandMass Aset N₀ T) =o[atTop] (fun T : ℝ => T))
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    (fun L => tailCharacterBandMass Aset N₀ α β L) =o[atTop] (fun L : ℝ => L) := by
  have hh := (harmonicQuadraticBandMass_isLittleO Aset N₀ α β hα (hα.trans hαβ) hquad).add
    (P0.higher_character_decorrelation hsize hM hAset hBset hsum N₀ hN₀ α β hα hαβ)
  simpa only [← tailCharacterBandMass_eq] using hh

/-- Markov's bound is uniform in subsets of the whole closed band. -/
theorem eventual_bad_tail_character_mass (A : Set ℕ) (N : ℕ) (α β δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε)
    (hsmall : (fun L => tailCharacterBandMass A N α β L) =o[atTop] (fun L : ℝ => L)) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, P ⊆ closedLogLogPrimeBand α β L →
      (∑ p ∈ P.filter (fun p => δ < tailCharacterBias A N p), (p : ℝ)⁻¹) ≤ ε * L := by
  have hh := hsmall.bound (mul_pos hδ hε)
  filter_upwards [hh, eventually_ge_atTop (0 : ℝ)] with L hh hL P hP
  have hnonneg : 0 ≤ tailCharacterBandMass A N α β L :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity) (tailCharacterBias_nonneg _ _ _))
  have hmass : tailCharacterBandMass A N α β L ≤ δ * ε * L := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hL] using hh
  apply (mul_le_mul_iff_right₀ hδ).mp
  calc
    δ * (∑ p ∈ P.filter (fun p => δ < tailCharacterBias A N p), (p : ℝ)⁻¹) =
        ∑ p ∈ P.filter (fun p => δ < tailCharacterBias A N p), δ * (p : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ P.filter (fun p => δ < tailCharacterBias A N p),
        (p : ℝ)⁻¹ * tailCharacterBias A N p := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := (Finset.mem_filter.mp hp).2.le
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (show 0 ≤ (p : ℝ)⁻¹ by positivity)
    _ ≤ tailCharacterBandMass A N α β L :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun p hp => hP (Finset.mem_filter.mp hp).1)
        (fun p _ _ => mul_nonneg (by positivity) (tailCharacterBias_nonneg A N p))
    _ ≤ δ * (ε * L) := by simpa only [mul_assoc] using hmass

end Ostmann

end OAI
