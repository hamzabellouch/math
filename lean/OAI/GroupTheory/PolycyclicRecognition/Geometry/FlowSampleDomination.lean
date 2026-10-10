import OAI.GroupTheory.PolycyclicRecognition.Geometry.FlowProbabilityCutoffs
import OAI.GroupTheory.PolycyclicRecognition.Geometry.OccupationFlowLimit

namespace OAI

/-! # Domination of all discrete microsteps by the fixed cutoff law -/

noncomputable section

namespace PolycyclicRecognition

open Filter MeasureTheory Set
open scoped Topology NNReal

theorem oneParameter_nat_mul {G : Type*} [Monoid G]
    (d : ℝ → G) (hd0 : d 0 = 1) (hmul : ∀ s t, d (s + t) = d s * d t)
    (t : ℝ) (n : ℕ) : d ((n : ℝ) * t) = d t ^ n := by
  induction n with
  | zero => simp [hd0]
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hmul, ih, pow_succ]

/-- All integer mesh starting times lie in the prescribed compact time
interval, including when the final interval is shorter than a mesh step. -/
theorem microstep_time_mem_Icc {r T : ℝ} (hr : 0 < r) (hT : 0 ≤ T)
    (L : ℕ) (hL : 0 < L) (j : Fin ⌊r * T / (L : ℝ)⌋₊) :
    (j : ℝ) * L / r ∈ Icc 0 T := by
  have hLr : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  have hj : (j : ℝ) ≤ (⌊r * T / (L : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast j.isLt.le
  have hfloor : (⌊r * T / (L : ℝ)⌋₊ : ℝ) * L ≤ r * T :=
    (le_div_iff₀ hLr).mp (Nat.floor_le (div_nonneg (mul_nonneg hr.le hT) hLr.le))
  refine ⟨div_nonneg (mul_nonneg (Nat.cast_nonneg _) hLr.le) hr.le, ?_⟩
  apply (div_le_iff₀ hr).mpr
  calc
    (j : ℝ) * L ≤ (⌊r * T / (L : ℝ)⌋₊ : ℝ) * L := mul_le_mul_of_nonneg_right hj hLr.le
    _ ≤ r * T := hfloor
    _ = T * r := mul_comm _ _

/-- Haar-preserving coordinate moves and the one fixed pair of cutoff
densities imply every domination premise of the two-limit argument. -/
theorem microstep_sample_laws_dominated
    {A V G ι : Type*} [MeasurableSpace A] [MeasurableSpace V]
    [Group G] [MetricSpace G] [ProperSpace G] [IsTopologicalGroup G]
    [IsIsometricSMul G G] {Λ : ℝ≥0}
    [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
    {l : Filter ι} (m : Measure V) (samples : ι → ProbabilityMeasure A)
    (η ρ : V → ℝ) (hiη : Integrable η m) (hiρ : Integrable ρ m)
    (hpη : ∀ z, 0 ≤ η z) (hpρ : ∀ z, 0 ≤ ρ z)
    (hmη : ∫ z, η z ∂m = 1) (hmρ : ∫ z, ρ z ∂m = 1) (hρ : Measurable ρ)
    (r : ι → ℝ) (hr : ∀ᶠ i in l, 0 < r i) {T : ℝ} (hT : 0 ≤ T)
    (F : ι → V × ℝ → V)
    (hpres : ∀ i t, MeasurePreserving (fun z => F i (z, t)) m m)
    (chart : ι → A × V → NormalizedPair G Λ) (hchart : ∀ i, Measurable (chart i))
    (d : ℝ → G) (hd0 : d 0 = 1) (hmul : ∀ s t, d (s + t) = d s * d t)
    (hmove : ∀ i a z t, (d (r i * t))⁻¹ • chart i (a, z) = chart i (a, F i (z, t)))
    (c : ℝ≥0)
    (hbound : ∀ᶠ i in l, ∀ t ∈ Icc 0 T, ∀ z, η z ≤ (c : ℝ) * ρ (F i (z, t))) :
    ∀ L : ℕ, 0 < L → ∀ᶠ i in l, ∀ j : Fin ⌊r i * T / (L : ℝ)⌋₊,
      Measure.map (fun p : NormalizedPair G Λ => (d L ^ (j : ℕ))⁻¹ • p)
        (productOccupationLaw (samples i) (densityProbabilityMeasure m η hiη hpη hmη)
          (chart i) : Measure _) ≤
      c • (productOccupationLaw (samples i) (densityProbabilityMeasure m ρ hiρ hpρ hmρ)
        (chart i) : Measure _) := by
  intro L hL
  filter_upwards [hr, hbound] with i hri hbi
  intro j
  let u := (j : ℝ) * L / r i
  have hu : u ∈ Icc 0 T := microstep_time_mem_Icc hri hT L hL j
  apply map_productOccupationLaw_le (samples i) _ _ (chart i) (hchart i)
    (fun z => F i (z, u)) (hpres i u).measurable
    (fun p => (d L ^ (j : ℕ))⁻¹ • p) (continuous_const_smul _).measurable
  · intro a z
    have htime : r i * u = (j : ℝ) * L := by dsimp [u]; field_simp
    simpa only [htime, oneParameter_nat_mul d hd0 hmul] using hmove i a z u
  · exact map_densityProbabilityMeasure_le m η ρ hiη hiρ hpη hpρ hmη hmρ
      hρ _ (hpres i u) c (hbi u hu)

end PolycyclicRecognition

end

end OAI
