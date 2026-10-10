import OAI.NumberTheory.TotientAsymptotic.BandGrid
import OAI.NumberTheory.TotientAsymptotic.BandPrimeError

namespace OAI

/-! Prime mass versus volume, with all remaining error confined to boundary boxes. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma gridInner_region_subset {N : ℕ} (K : Finset (Fin N → ℕ)) (S : Set (Fin N → ℝ)) :
    gridRegion (gridInner K S) ⊆ S := by
  intro u hu
  obtain ⟨m, hu⟩ := Set.mem_iUnion.mp hu
  obtain ⟨hm, hu⟩ := Set.mem_iUnion.mp hu
  exact (Finset.mem_filter.mp hm).2 hu

lemma gridOuter_region_covers {N : ℕ} (K : Finset (Fin N → ℕ)) (S : Set (Fin N → ℝ))
    (hS : S ⊆ gridRegion K) : S ⊆ gridRegion (gridOuter K S) := by
  intro u hu
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (hS hu)
  obtain ⟨hm, hum⟩ := Set.mem_iUnion.mp hm
  exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr
    ⟨Finset.mem_filter.mpr ⟨hm, u, hum, hu⟩, hum⟩⟩

lemma grid_volume_sandwich {N : ℕ} (K : Finset (Fin N → ℕ)) (S : Set (Fin N → ℝ))
    (hS : S ⊆ gridRegion K) :
    ((gridInner K S).card : ℝ) ≤ (volume S).toReal ∧
      (volume S).toReal ≤ (gridOuter K S).card := by
  have ho : volume (gridRegion (gridOuter K S)) ≠ ⊤ := by
    rw [volume_gridRegion]
    exact ENNReal.natCast_ne_top _
  have hfin : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top ho (measure_mono (gridOuter_region_covers K S hS))
  constructor
  · simpa only [measureReal_def, gridRegion_volume_real] using
      (measureReal_mono (μ := volume) (gridInner_region_subset K S) hfin)
  · simpa only [measureReal_def, gridRegion_volume_real] using
      (measureReal_mono (μ := volume) (gridOuter_region_covers K S hS) ho)

lemma grid_restricted_mass_error {N : ℕ} (K : Finset (Fin N → ℕ))
    (S : Set (Fin N → ℝ)) (hS : S ⊆ gridRegion K) {e : ℝ} (he : 0 ≤ e)
    (hi : |gridPrimeMass (gridInner K S)-(gridInner K S).card| ≤ (gridInner K S).card*e)
    (ho : |gridPrimeMass (gridOuter K S)-(gridOuter K S).card| ≤ (gridOuter K S).card*e) :
    |gridRestrictedPrimeMass K S-(volume S).toReal| ≤
      (gridOuter K S).card*e+((gridOuter K S).card-(gridInner K S).card) := by
  have hm := grid_prime_mass_sandwich K S
  have hv := grid_volume_sandwich K S hS
  have hc : ((gridInner K S).card : ℝ) ≤ (gridOuter K S).card := by
    exact_mod_cast Finset.card_le_card (gridInner_subset_outer K S)
  have hi' := (abs_le.mp hi).1
  have ho' := (abs_le.mp ho).2
  have hmul := mul_le_mul_of_nonneg_right hc he
  rw [abs_le]
  constructor <;> linarith

lemma bandPrimeError_nonneg {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (H : ℕ) :
    0 ≤ bandPrimeError C c H := by
  unfold bandPrimeError
  have hq : Real.exp (-c*lam) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [lam_pos]
  have he : 0 ≤ C*(Real.exp (-c*lam)^H/(1-Real.exp (-c*lam))) := by positivity
  exact sub_nonneg.mpr (Real.one_le_exp he)

/-- For every subset of the retained bands, the only error beyond the prime
box estimate is the number of boxes crossing its boundary. -/
theorem banded_restricted_mass_error (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x : ℝ} {H : ℕ}, 0 ≤ theta x → H ≤ m x →
      ∀ S : Set (Fin (R x H) → ℝ), S ⊆ prefixBandRegion x H →
      |gridRestrictedPrimeMass (bandGrid x H) S-(volume S).toReal| ≤
        (gridOuter (bandGrid x H) S).card*bandPrimeError C (9/10) H+
          ((gridOuter (bandGrid x H) S).card-(gridInner (bandGrid x H) S).card) := by
  obtain ⟨C, hC, hgrid⟩ := banded_grid_prime_mass_error hford
  refine ⟨C, hC, ?_⟩
  intro x H hθ hHm S hS
  have hi := hgrid hθ (by norm_num : (0 : ℝ)<9/10) hHm (gridInner (bandGrid x H) S)
    (fun b hb i => bandGrid_bounds (Finset.mem_filter.mp hb).1 i)
  have ho := hgrid hθ (by norm_num : (0 : ℝ)<9/10) hHm (gridOuter (bandGrid x H) S)
    (fun b hb i => bandGrid_bounds (Finset.mem_filter.mp hb).1 i)
  simp only [gridRegion_volume_real] at hi ho
  exact grid_restricted_mass_error _ S (hS.trans (prefixBandRegion_covered x H))
    (bandPrimeError_nonneg hC.le (by norm_num) H) hi ho

def bandedVolumeMass (x : ℝ) (H : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (tailValueBound H), f ((ell d : ℝ)/d)/d *
    (volume (bandedWitnessRegion x H d)).toReal

/-- A finite quantitative mass-to-volume estimate for the genuine witness
unions. The bound is uniform over weights between zero and one. -/
theorem mass_banded_volume_error (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x : ℝ} {H : ℕ}, P H < H → H ≤ m x →
      theta x ∈ Set.Ico (0 : ℝ) 1 → ∀ f : ℝ → ℝ,
      (∀ r, 0 ≤ f r ∧ f r ≤ 1) →
      |M x H f-bandedVolumeMass x H f| ≤
        ∑ d ∈ Finset.Icc 1 (tailValueBound H), (d : ℝ)⁻¹*
          ((gridOuter (bandGrid x H) (bandedWitnessRegion x H d)).card*bandPrimeError C (9/10) H+
            ((gridOuter (bandGrid x H) (bandedWitnessRegion x H d)).card-
              (gridInner (bandGrid x H) (bandedWitnessRegion x H d)).card)) := by
  obtain ⟨C, hC, herr⟩ := banded_restricted_mass_error hford
  refine ⟨C, hC, ?_⟩
  intro x H hPH hHm hθ f hf
  rw [mass_eq_banded_grid_sum hPH hHm hθ, bandedVolumeMass, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  have hderr := herr hθ.1 hHm (bandedWitnessRegion x H d) (fun _ hu => hu.1)
  have hden : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hw : 0 ≤ f ((ell d : ℝ)/d)/d := div_nonneg (hf _).1 hden.le
  have hw' : f ((ell d : ℝ)/d)/d ≤ (d : ℝ)⁻¹ := by
    simpa only [one_div] using div_le_div_of_nonneg_right (hf _).2 hden.le
  rw [← mul_sub, abs_mul, abs_of_nonneg hw]
  exact (mul_le_mul_of_nonneg_left hderr hw).trans
    (mul_le_mul_of_nonneg_right hw' ((abs_nonneg _).trans hderr))

end TotientAsymptotic

end

end OAI
