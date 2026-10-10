import OAI.Combinatorics.BalancedRyser.Profiles.ProfileAmbientCompactness
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileEmpirical

namespace OAI

noncomputable section
namespace Balanced.ProfileEmpiricalSupport
open MeasureTheory Filter Topology
open scoped NNReal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem empiricalProfileMeasure_compl_eq_zero
    (D C E : Finset (Line F)) {K : Set Profile} (hK : MeasurableSet K)
    (hE : ∀ l ∈ E, lineProfile D C l ∈ K) :
    empiricalProfileMeasure D C E Kᶜ = 0 := by
  rw [FiniteMeasure.null_iff_toMeasure_null]
  change (((Fintype.card F : ℝ≥0)⁻¹ •
    ∑ line ∈ E, profileDirac (lineProfile D C line) : FiniteMeasure Profile) :
      Measure Profile) Kᶜ = 0
  rw [FiniteMeasure.toMeasure_smul, FiniteMeasure.toMeasure_sum,
    Measure.smul_apply, Measure.finsetSum_apply]
  change (Fintype.card F : ℝ≥0)⁻¹ •
    (∑ line ∈ E, Measure.dirac (lineProfile D C line) Kᶜ) = 0
  have hz : ∑ l ∈ E, Measure.dirac (lineProfile D C l) Kᶜ = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    rw [Measure.dirac_apply' _ hK.compl]
    simp [hE l hl]
  rw [hz]
  simp

theorem empiricalProfileMeasure_bounded_support
    (D C E : Finset (Line F)) {M : ℝ} (hM : 0 ≤ M)
    (hE : ∀ l ∈ E, IsBoundedProfile M (lineProfile D C l)) :
    empiricalProfileMeasure D C E {p | IsBoundedProfile M p}ᶜ = 0 :=
  empiricalProfileMeasure_compl_eq_zero D C E
    (ProfileAmbientCompactness.isClosed_boundedProfiles M hM).measurableSet hE

theorem admissible_empirical_bounded_support
    (k : ℕ) (D C E : Finset (Line F)) (hD : IsDeletionSet k D)
    (hC : C.card ≤ Fintype.card F) :
    empiricalProfileMeasure D C E {p | IsBoundedProfile (2 * (k : ℝ) + 4) p}ᶜ = 0 :=
  empiricalProfileMeasure_bounded_support D C E (by positivity)
    (fun l _ => lineProfile_isBounded k D C l hD hC)

theorem profileSequenceLimit_bounded
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) :
    IsBoundedProfile (2 * (k : ℝ) + 4) P ∧
    (∀ᵐ p ∂νD.toMeasure, IsBoundedProfile (2 * (k : ℝ) + 4) p) ∧
    (∀ᵐ p ∂νC.toMeasure, IsBoundedProfile (2 * (k : ℝ) + 4) p) := by
  have hM : 0 ≤ 2 * (k : ℝ) + 4 := by positivity
  refine ⟨ProfileAmbientCompactness.boundedProfile_of_tendsto hM
    (fun n => planeProfile_isBounded k (D n) (C n) (hpair n).1 (hpair n).2.2)
    ht.2.1, ?_, ?_⟩
  · exact ProfileAmbientCompactness.ae_boundedProfile_of_tendsto hM
      (fun n => admissible_empirical_bounded_support k (D n) (C n) (D n)
        (hpair n).1 (hpair n).2.2) ht.2.2.1
  · exact ProfileAmbientCompactness.ae_boundedProfile_of_tendsto hM
      (fun n => admissible_empirical_bounded_support k (D n) (C n) (C n)
        (hpair n).1 (hpair n).2.2) ht.2.2.2

theorem lineProfile_zero_first_of_mem (D C : Finset (Line F))
    (l : Line F) (hl : l ∈ D) (j : ℕ) : lineProfile D C l (0, j) = 0 := by
  have he : (linePoints l).filter (fun x =>
      lineMultiplicity D x = 0 ∧ lineMultiplicity C x = j) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx hxi
    have hxline : OnLine x l := (Finset.mem_filter.mp hx).2
    have hpos : 0 < (D.filter (fun m => OnLine x m)).card :=
      Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, hxline⟩⟩
    have hz := hxi.1
    change (D.filter (fun m => OnLine x m)).card = 0 at hz
    omega
  simp only [lineProfile, he, Finset.card_empty, Nat.cast_zero, zero_div]

theorem lineProfile_zero_second_of_mem (D C : Finset (Line F))
    (l : Line F) (hl : l ∈ C) (i : ℕ) : lineProfile D C l (i, 0) = 0 := by
  have he : (linePoints l).filter (fun x =>
      lineMultiplicity D x = i ∧ lineMultiplicity C x = 0) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx hxi
    have hxline : OnLine x l := (Finset.mem_filter.mp hx).2
    have hpos : 0 < (C.filter (fun m => OnLine x m)).card :=
      Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, hxline⟩⟩
    have hz := hxi.2
    change (C.filter (fun m => OnLine x m)).card = 0 at hz
    omega
  simp only [lineProfile, he, Finset.card_empty, Nat.cast_zero, zero_div]

theorem profileSequenceLimit_zero_coordinates
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) :
    (∀ᵐ p ∂νD.toMeasure, ∀ j : ℕ, p (0,j) = 0) ∧
    (∀ᵐ p ∂νC.toMeasure, ∀ i : ℕ, p (i,0) = 0) := by
  have hM : 0 ≤ 2 * (k : ℝ) + 4 := by positivity
  have hK := ProfileAmbientCompactness.isCompact_boundedProfiles _ hM
  have hZ₁ : IsClosed {p : Profile | ∀ j : ℕ, p (0,j) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_eq (continuous_apply (0,j)) continuous_const
  have hZ₂ : IsClosed {p : Profile | ∀ i : ℕ, p (i,0) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq (continuous_apply (i,0)) continuous_const
  have hK₁ := hK.inter_right hZ₁
  have hK₂ := hK.inter_right hZ₂
  constructor
  · have hzero := ProfileAmbientCompactness.compact_support_of_tendsto hK₁
      (μ := fun n => empiricalProfileMeasure (D n) (C n) (D n))
      (fun n => empiricalProfileMeasure_compl_eq_zero (D n) (C n) (D n)
        hK₁.measurableSet (fun l hl =>
          ⟨lineProfile_isBounded k (D n) (C n) l (hpair n).1 (hpair n).2.2,
            lineProfile_zero_first_of_mem (D n) (C n) l hl⟩)) ht.2.2.1
    have hae := ae_iff.mpr ((FiniteMeasure.null_iff_toMeasure_null νD _).mp hzero)
    exact hae.mono fun _ hp => hp.2
  · have hzero := ProfileAmbientCompactness.compact_support_of_tendsto hK₂
      (μ := fun n => empiricalProfileMeasure (D n) (C n) (C n))
      (fun n => empiricalProfileMeasure_compl_eq_zero (D n) (C n) (C n)
        hK₂.measurableSet (fun l hl =>
          ⟨lineProfile_isBounded k (D n) (C n) l (hpair n).1 (hpair n).2.2,
            lineProfile_zero_second_of_mem (D n) (C n) l hl⟩)) ht.2.2.2
    have hae := ae_iff.mpr ((FiniteMeasure.null_iff_toMeasure_null νC _).mp hzero)
    exact hae.mono fun _ hp => hp.2

end Balanced.ProfileEmpiricalSupport

end

end OAI
