import OAI.Combinatorics.BalancedRyser.Incidence.AffineProfileIncidence
import OAI.Combinatorics.BalancedRyser.Incidence.FiniteProfileIncidence
import OAI.Combinatorics.BalancedRyser.Profiles.Profile

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology
open scoped BigOperators ENNReal NNReal

namespace Balanced.FiniteProfile

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem lineProfile_mem_Icc (D C : Finset (Line F)) (l : Line F) (ij : ℕ × ℕ) :
    lineProfile D C l ij ∈ Set.Icc (0 : ℝ) 1 := by
  dsimp [lineProfile]
  refine ⟨by positivity, ?_⟩
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  apply (div_le_one hq).mpr
  have h := Finset.card_filter_le (linePoints l) (fun p ↦
    lineMultiplicity D p = ij.1 ∧ lineMultiplicity C p = ij.2)
  rw [linePoints_card] at h
  exact_mod_cast h

theorem planeProfile_mem_Icc (D C : Finset (Line F)) (ij : ℕ × ℕ) :
    planeProfile D C ij ∈ Set.Icc (0 : ℝ) 1 := by
  dsimp [planeProfile]
  refine ⟨by positivity, ?_⟩
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  apply (div_le_one (sq_pos_of_pos hq)).mpr
  have h := Finset.card_filter_le (Finset.univ : Finset (Point F)) (fun p ↦
    lineMultiplicity D p = ij.1 ∧ lineMultiplicity C p = ij.2)
  have hc : (Finset.univ : Finset (Point F)).card = (Fintype.card F) ^ 2 := by
    simp [Point, pow_two]
  rw [hc] at h
  exact_mod_cast h

theorem coe_empiricalProfileMeasure (D C E : Finset (Line F)) :
    (empiricalProfileMeasure D C E : Measure Profile) =
      ENNReal.ofReal ((Fintype.card F : ℝ)⁻¹) •
        ∑ l ∈ E, Measure.dirac (lineProfile D C l) := by
  let weight : ℝ≥0 := ⟨(Fintype.card F : ℝ)⁻¹, by positivity⟩
  change weight •
    ((∑ l ∈ E, profileDirac (lineProfile D C l) : FiniteMeasure Profile) :
      Measure Profile) = _
  rw [FiniteMeasure.toMeasure_sum]
  rw [← Measure.coe_nnreal_smul, ENNReal.coe_nnreal_eq]
  rfl

theorem empiricalProfileMeasure_integral (D C E : Finset (Line F))
    (f : Profile → ℝ) :
    (∫ x, f x ∂(empiricalProfileMeasure D C E : Measure Profile)) =
      (Fintype.card F : ℝ)⁻¹ * ∑ l ∈ E, f (lineProfile D C l) := by
  rw [coe_empiricalProfileMeasure]
  exact integral_empirical_profile E (lineProfile D C) f _ (by positivity)

theorem empiricalProfileMeasure_mass (D C E : Finset (Line F)) :
    (empiricalProfileMeasure D C E : Measure Profile).real Set.univ =
      (E.card : ℝ) / (Fintype.card F : ℝ) := by
  have h := empiricalProfileMeasure_integral D C E (fun _ ↦ 1)
  simpa [div_eq_mul_inv, mul_comm] using h

theorem empiricalProfileMeasure_deletion_incidence (D C : Finset (Line F))
    (i j : ℕ) :
    (∫ x, x (i, j) ∂(empiricalProfileMeasure D C D : Measure Profile)) =
      (i : ℝ) * planeProfile D C (i, j) := by
  rw [empiricalProfileMeasure_integral, mul_comm, ← div_eq_mul_inv]
  exact deletion_coordinate_incidence_real D C i j

theorem empiricalProfileMeasure_cover_incidence (D C : Finset (Line F))
    (i j : ℕ) :
    (∫ x, x (i, j) ∂(empiricalProfileMeasure D C C : Measure Profile)) =
      (j : ℝ) * planeProfile D C (i, j) := by
  rw [empiricalProfileMeasure_integral, mul_comm, ← div_eq_mul_inv]
  exact cover_coordinate_incidence_real D C i j

theorem ae_empiricalProfileMeasure_of_forall (D C E : Finset (Line F))
    (Q : Profile → Prop) (hQ : ∀ l ∈ E, Q (lineProfile D C l)) :
    ∀ᵐ x ∂(empiricalProfileMeasure D C E : Measure Profile), Q x := by
  rw [coe_empiricalProfileMeasure]
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro l hl
  simpa only [ae_dirac_eq, Filter.eventually_pure] using hQ l hl

theorem empiricalProfileMeasure_unit_coordinates (D C E : Finset (Line F)) :
    ∀ᵐ x ∂(empiricalProfileMeasure D C E : Measure Profile),
      ∀ ij, x ij ∈ Set.Icc (0 : ℝ) 1 := by
  apply ae_empiricalProfileMeasure_of_forall
  intro l _ ij
  exact lineProfile_mem_Icc D C l ij

theorem empiricalProfileMeasure_deletion_zero_row (D C : Finset (Line F)) :
    ∀ᵐ x ∂(empiricalProfileMeasure D C D : Measure Profile), ∀ j, x (0, j) = 0 := by
  apply ae_empiricalProfileMeasure_of_forall
  intro l hl j
  change (((linePoints l).filter (fun p ↦
    deletionMultiplicity D p = 0 ∧ deletionMultiplicity C p = j)).card : ℝ) /
      (Fintype.card F : ℝ) = 0
  rw [deletion_line_zero_row D C hl]
  simp

theorem empiricalProfileMeasure_cover_zero_column (D C : Finset (Line F)) :
    ∀ᵐ x ∂(empiricalProfileMeasure D C C : Measure Profile), ∀ i, x (i, 0) = 0 := by
  apply ae_empiricalProfileMeasure_of_forall
  intro l hl i
  change (((linePoints l).filter (fun p ↦
    deletionMultiplicity D p = i ∧ deletionMultiplicity C p = 0)).card : ℝ) /
      (Fintype.card F : ℝ) = 0
  rw [cover_line_zero_column D C hl]
  simp

theorem empiricalProfileMeasure_deletion_mass (D C : Finset (Line F))
    {k : ℕ} (hD : IsDeletionSet k D) :
    (empiricalProfileMeasure D C D : Measure Profile).real Set.univ =
      (k : ℝ) + (k : ℝ) * (Fintype.card F : ℝ)⁻¹ := by
  rw [empiricalProfileMeasure_mass, deletionSet_card hD]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  push_cast
  field_simp

theorem empiricalProfileMeasure_deletion_mass_tendsto
    {K : ℕ → Type*} [∀ n, Field (K n)] [∀ n, Fintype (K n)]
    [∀ n, DecidableEq (K n)]
    (D C : ∀ n, Finset (Line (K n))) {k : ℕ}
    (hD : ∀ n, IsDeletionSet k (D n))
    (hq : Tendsto (fun n ↦ Fintype.card (K n)) atTop atTop) :
    Tendsto (fun n ↦ (empiricalProfileMeasure (D n) (C n) (D n) :
      Measure Profile).real Set.univ) atTop (𝓝 (k : ℝ)) := by
  have hqR : Tendsto (fun n ↦ (Fintype.card (K n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have hinv : Tendsto (fun n ↦ (Fintype.card (K n) : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hqR
  have ht := (tendsto_const_nhds (x := (k : ℝ))).add
    ((tendsto_const_nhds (x := (k : ℝ))).mul hinv)
  simpa only [empiricalProfileMeasure_deletion_mass (D _) (C _) (hD _),
    mul_zero, add_zero] using ht

end Balanced.FiniteProfile

end

end OAI
