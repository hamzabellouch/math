import OAI.Combinatorics.BalancedRyser.Profiles.ProfileEmpirical
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileWeakCompactness

namespace OAI

noncomputable section
open Finset MeasureTheory Filter
open scoped NNReal Topology

namespace Balanced
open scoped _root_.Balanced

def finiteDirac {X : Type*} [MeasurableSpace X] (x : X) : FiniteMeasure X :=
  ⟨Measure.dirac x, inferInstance⟩

theorem scaled_dirac_sum_mass {α X : Type*} [MeasurableSpace X]
    (a : ℝ≥0) (s : Finset α) (f : α → X) :
    (((a • ∑ i ∈ s, finiteDirac (f i)).mass) : ℝ) =
      (a : ℝ) * s.card := by
  have hmass :
      (((a • ∑ i ∈ s, finiteDirac (f i)) :
        FiniteMeasure X) : Measure X) Set.univ = (a : ENNReal) * s.card := by
    rw [FiniteMeasure.toMeasure_smul, FiniteMeasure.toMeasure_sum, Measure.smul_apply,
      Measure.finsetSum_apply]
    simp only [finiteDirac, FiniteMeasure.toMeasure, Measure.dirac_apply_of_mem (Set.mem_univ _),
      Finset.sum_const, nsmul_eq_mul, mul_one, ENNReal.smul_def, smul_eq_mul]
  calc
    _ = ((((a • ∑ i ∈ s, finiteDirac (f i)) :
        FiniteMeasure X) : Measure X) Set.univ).toReal := by
      rw [← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal]
    _ = (a : ℝ) * s.card := by rw [hmass]; simp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem empiricalProfileMeasure_mass (D C E : Finset (Line F)) :
    ((empiricalProfileMeasure D C E).mass : ℝ) =
      (E.card : ℝ) / (Fintype.card F : ℝ) := by
  have h := scaled_dirac_sum_mass
    (⟨(Fintype.card F : ℝ)⁻¹, by positivity⟩ : ℝ≥0) E (lineProfile D C)
  change ((empiricalProfileMeasure D C E).mass : ℝ) = _ at h
  convert! h using 1
  change (E.card : ℝ) / (Fintype.card F : ℝ) = (Fintype.card F : ℝ)⁻¹ * E.card
  ring

theorem isBoundedProfile_iff_mem_profiles (M : ℝ) (P : Profile) :
    IsBoundedProfile M P ↔ P ∈ ProfileMomentCompactness.profiles M := by
  rw [ProfileMomentCompactness.mem_profiles_iff]
  simp only [IsBoundedProfile, ProfileMomentCompactness.weight, Nat.cast_add]

abbrev BoundedProfile (M : ℝ) := ProfileMomentCompactness.profiles M

def boundedLineProfile (k : ℕ) (D C : Finset (Line F)) (l : Line F)
    (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F) :
    BoundedProfile (2 * (k : ℝ) + 4) :=
  ⟨lineProfile D C l, (isBoundedProfile_iff_mem_profiles _ _).mp
    (lineProfile_isBounded k D C l hD hC)⟩

def boundedEmpiricalProfileMeasure (k : ℕ) (D C E : Finset (Line F))
    (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F) :
    FiniteMeasure (BoundedProfile (2 * (k : ℝ) + 4)) := by
  let a : ℝ≥0 := ⟨(Fintype.card F : ℝ)⁻¹, by positivity⟩
  let ν : FiniteMeasure (BoundedProfile (2 * (k : ℝ) + 4)) :=
    ∑ l ∈ E, ⟨Measure.dirac (boundedLineProfile k D C l hD hC), inferInstance⟩
  exact a • ν

theorem boundedEmpiricalProfileMeasure_mass (k : ℕ) (D C E : Finset (Line F))
    (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F) :
    ((boundedEmpiricalProfileMeasure k D C E hD hC).mass : ℝ) =
      (E.card : ℝ) / (Fintype.card F : ℝ) := by
  have h := scaled_dirac_sum_mass
    (⟨(Fintype.card F : ℝ)⁻¹, by positivity⟩ : ℝ≥0) E
    (fun l => boundedLineProfile k D C l hD hC)
  change ((boundedEmpiricalProfileMeasure k D C E hD hC).mass : ℝ) = _ at h
  convert! h using 1
  change (E.card : ℝ) / (Fintype.card F : ℝ) = (Fintype.card F : ℝ)⁻¹ * E.card
  ring

theorem finiteDirac_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) (x : X) :
    (finiteDirac x).map f = finiteDirac (f x) := by
  apply FiniteMeasure.toMeasure_injective
  change (Measure.dirac x).map f = Measure.dirac (f x)
  exact Measure.map_dirac' hf x

theorem scaled_dirac_sum_map {α X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (a : ℝ≥0) (s : Finset α) (g : α → X) (f : X → Y) (hf : Measurable f) :
    (a • ∑ i ∈ s, finiteDirac (g i)).map f =
      a • ∑ i ∈ s, finiteDirac (f (g i)) := by
  change (FiniteMeasure.mapHom hf) (a • ∑ i ∈ s, finiteDirac (g i)) = _
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact finiteDirac_map f hf (g i)

theorem boundedEmpiricalProfileMeasure_map (k : ℕ) (D C E : Finset (Line F))
    (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F) :
    (boundedEmpiricalProfileMeasure k D C E hD hC).map Subtype.val =
      empiricalProfileMeasure D C E := by
  exact scaled_dirac_sum_map
    (⟨(Fintype.card F : ℝ)⁻¹, by positivity⟩ : ℝ≥0) E
    (fun l => boundedLineProfile k D C l hD hC) Subtype.val measurable_subtype_coe

def boundedPlaneProfile (k : ℕ) (D C : Finset (Line F))
    (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F) :
    BoundedProfile (2 * (k : ℝ) + 4) :=
  ⟨planeProfile D C, (isBoundedProfile_iff_mem_profiles _ _).mp
    (planeProfile_isBounded k D C hD hC)⟩

omit [DecidableEq F] in

theorem profile_witness_ratio_mem_Icc (C : Finset (Line F))
    (hC : C.card ≤ Fintype.card F) :
    (C.card : ℝ) / (Fintype.card F : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨by positivity, ?_⟩
  apply (div_le_one (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card F)).2
  exact_mod_cast hC

theorem boundedEmpiricalProfileMeasure_deletion_mass_le (k : ℕ)
    (D C : Finset (Line F)) (hD : IsDeletionSet k D) (hC : C.card ≤ Fintype.card F) :
    ((boundedEmpiricalProfileMeasure k D C D hD hC).mass : ℝ) ≤ 2 * (k : ℝ) := by
  rw [boundedEmpiricalProfileMeasure_mass, profile_deletionSet_card k D hD]
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hqone : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  apply (div_le_iff₀ hq).2
  push_cast
  have hmul : 0 ≤ (k : ℝ) * ((Fintype.card F : ℝ) - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hqone)
  nlinarith

theorem exists_actual_profile_subsequence
    {K : ℕ → Type*} [∀ n, Field (K n)] [∀ n, Fintype (K n)]
    [∀ n, DecidableEq (K n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (K n)))
    (hD : ∀ n, IsDeletionSet k (D n))
    (hC : ∀ n, (C n).card ≤ Fintype.card (K n)) :
    ∃ c ∈ Set.Icc (0 : ℝ) 1, ∃ P : Profile,
      IsBoundedProfile (2 * (k : ℝ) + 4) P ∧
      ∃ νD νC : FiniteMeasure Profile, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ProfileSequenceLimit (fun n => D (φ n)) (fun n => C (φ n)) c P νD νC := by
  let M : ℝ := 2 * (k : ℝ) + 4
  let ratio : ℕ → ℝ := fun n => ((C n).card : ℝ) / (Fintype.card (K n) : ℝ)
  let p : ℕ → BoundedProfile M := fun n => boundedPlaneProfile k (D n) (C n) (hD n) (hC n)
  let μ : ℕ → FiniteMeasure (BoundedProfile M) := fun n =>
    boundedEmpiricalProfileMeasure k (D n) (C n) (D n) (hD n) (hC n)
  let ν : ℕ → FiniteMeasure (BoundedProfile M) := fun n =>
    boundedEmpiricalProfileMeasure k (D n) (C n) (C n) (hD n) (hC n)
  let B : ℝ≥0 := ⟨2 * (k : ℝ), by positivity⟩
  have hμ : ∀ n, (μ n).mass ≤ B := by
    intro n
    apply NNReal.coe_le_coe.mp
    exact boundedEmpiricalProfileMeasure_deletion_mass_le k (D n) (C n) (hD n) (hC n)
  have hν : ∀ n, (ν n).mass ≤ 1 := by
    intro n
    apply NNReal.coe_le_coe.mp
    change ((boundedEmpiricalProfileMeasure k (D n) (C n) (C n) (hD n) (hC n)).mass : ℝ) ≤ 1
    rw [boundedEmpiricalProfileMeasure_mass]
    exact (profile_witness_ratio_mem_Icc (C n) (hC n)).2
  obtain ⟨c, hc, P, μ₀, ν₀, _, _, φ, hφ, hratio, hp, hμlim, hνlim⟩ :=
    ProfileWeakCompactness.exists_full_profile_subsequence M (by positivity)
      ratio (fun n => profile_witness_ratio_mem_Icc (C n) (hC n)) p B 1 μ ν hμ hν
  refine ⟨c, hc, P.val, (isBoundedProfile_iff_mem_profiles _ _).mpr P.property,
    μ₀.map Subtype.val, ν₀.map Subtype.val, φ, hφ, ?_⟩
  refine ⟨hratio, ?_, ?_, ?_⟩
  · exact (continuous_subtype_val.tendsto P).comp hp
  · have ht := FiniteMeasure.tendsto_map_of_tendsto_of_continuous
      (μ ∘ φ) μ₀ hμlim continuous_subtype_val
    have he : (fun n => (μ (φ n)).map Subtype.val) =
        (fun n => empiricalProfileMeasure (D (φ n)) (C (φ n)) (D (φ n))) := by
      funext n
      exact boundedEmpiricalProfileMeasure_map k _ _ _ (hD (φ n)) (hC (φ n))
    change Tendsto (fun n => (μ (φ n)).map Subtype.val) atTop _ at ht
    rw [he] at ht
    exact ht
  · have ht := FiniteMeasure.tendsto_map_of_tendsto_of_continuous
      (ν ∘ φ) ν₀ hνlim continuous_subtype_val
    have he : (fun n => (ν (φ n)).map Subtype.val) =
        (fun n => empiricalProfileMeasure (D (φ n)) (C (φ n)) (C (φ n))) := by
      funext n
      exact boundedEmpiricalProfileMeasure_map k _ _ _ (hD (φ n)) (hC (φ n))
    change Tendsto (fun n => (ν (φ n)).map Subtype.val) atTop _ at ht
    rw [he] at ht
    exact ht

end Balanced

end

end OAI
