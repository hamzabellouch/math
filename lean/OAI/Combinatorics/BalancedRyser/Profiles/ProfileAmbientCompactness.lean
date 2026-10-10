import OAI.Combinatorics.BalancedRyser.Profiles.Profile
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileWeakCompactness

namespace OAI

noncomputable section
namespace Balanced.ProfileAmbientCompactness
open Filter Topology TopologicalSpace MeasureTheory
open scoped NNReal

theorem boundedProfiles_eq (M : ℝ) :
    {p : Profile | IsBoundedProfile M p} = ProfileMomentCompactness.profiles M := by
  ext p
  rw [ProfileMomentCompactness.mem_profiles_iff]
  simp only [Set.mem_ofPred_eq, IsBoundedProfile, ProfileMomentCompactness.weight,
    Nat.cast_add]

theorem isCompact_boundedProfiles (M : ℝ) (hM : 0 ≤ M) :
    IsCompact {p : Profile | IsBoundedProfile M p} := by
  rw [boundedProfiles_eq]
  exact ProfileMomentCompactness.isCompact_profiles M hM

theorem isClosed_boundedProfiles (M : ℝ) (hM : 0 ≤ M) :
    IsClosed {p : Profile | IsBoundedProfile M p} :=
  (isCompact_boundedProfiles M hM).isClosed

theorem boundedProfile_of_tendsto {M : ℝ} (hM : 0 ≤ M)
    {p : ℕ → Profile} {P : Profile}
    (hp : ∀ n, IsBoundedProfile M (p n)) (ht : Tendsto p atTop (𝓝 P)) :
    IsBoundedProfile M P :=
  (isClosed_boundedProfiles M hM).mem_of_tendsto ht (Eventually.of_forall hp)

theorem compact_support_of_tendsto
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [T2Space E] [PseudoMetrizableSpace E]
    {K : Set E} (hK : IsCompact K)
    {μ : ℕ → FiniteMeasure E} {ν : FiniteMeasure E}
    (hμ : ∀ n, μ n Kᶜ = 0) (ht : Tendsto μ atTop (𝓝 ν)) :
    ν Kᶜ = 0 := by
  have hm : ∀ᶠ n in atTop, (μ n).mass ≤ ν.mass + 1 := by
    exact (ht.mass.eventually (eventually_lt_nhds (lt_add_one ν.mass))).mono
      (fun _ h => h.le)
  have hc := isCompact_setOfPred_finiteMeasure_le_of_isCompact (ν.mass + 1) hK
  have hmem : ν ∈ {η : FiniteMeasure E | η.mass ≤ ν.mass + 1 ∧ η Kᶜ = 0} := by
    apply hc.isClosed.mem_of_tendsto ht
    filter_upwards [hm] with n hn
    exact ⟨hn, hμ n⟩
  exact hmem.2

theorem boundedProfile_support_of_tendsto {M : ℝ} (hM : 0 ≤ M)
    {μ : ℕ → FiniteMeasure Profile} {ν : FiniteMeasure Profile}
    (hμ : ∀ n, μ n {p | IsBoundedProfile M p}ᶜ = 0)
    (ht : Tendsto μ atTop (𝓝 ν)) :
    ν {p | IsBoundedProfile M p}ᶜ = 0 :=
  compact_support_of_tendsto (isCompact_boundedProfiles M hM) hμ ht

theorem ae_boundedProfile_of_tendsto {M : ℝ} (hM : 0 ≤ M)
    {μ : ℕ → FiniteMeasure Profile} {ν : FiniteMeasure Profile}
    (hμ : ∀ n, μ n {p | IsBoundedProfile M p}ᶜ = 0)
    (ht : Tendsto μ atTop (𝓝 ν)) :
    ∀ᵐ p ∂ν.toMeasure, IsBoundedProfile M p := by
  apply ae_iff.mpr
  exact (FiniteMeasure.null_iff_toMeasure_null ν _).mp
    (boundedProfile_support_of_tendsto hM hμ ht)

theorem map_comap_subtype
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hK : IsClosed K) (μ : FiniteMeasure E)
    (hμ : μ Kᶜ = 0) :
    (μ.comap (Subtype.val : K → E)).map Subtype.val = μ := by
  apply FiniteMeasure.toMeasure_injective
  simp only [FiniteMeasure.toMeasure_map, FiniteMeasure.toMeasure_comap]
  rw [map_comap_subtype_coe hK.measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem
    ((FiniteMeasure.null_iff_toMeasure_null μ Kᶜ).mp hμ)

theorem map_subtype_support
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hK : IsClosed K) (μ : FiniteMeasure K) :
    (μ.map (Subtype.val : K → E)) Kᶜ = 0 := by
  rw [FiniteMeasure.null_iff_toMeasure_null, FiniteMeasure.toMeasure_map,
    Measure.map_apply measurable_subtype_coe hK.measurableSet.compl]
  simp

theorem nonempty_boundedProfiles (M : ℝ) (hM : 0 ≤ M) :
    Nonempty {p : Profile | IsBoundedProfile M p} := by
  rw [boundedProfiles_eq]
  exact ProfileWeakCompactness.nonempty_profiles M hM

theorem exists_ambient_profile_measure_subsequence (M : ℝ) (hM : 0 ≤ M)
    (C : ℝ≥0) (μ : ℕ → FiniteMeasure Profile)
    (hμ : ∀ n, (μ n).mass ≤ C)
    (hs : ∀ n, μ n {p | IsBoundedProfile M p}ᶜ = 0) :
    ∃ ν : FiniteMeasure Profile, ν.mass ≤ C ∧
      ν {p | IsBoundedProfile M p}ᶜ = 0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  let K := {p : Profile | IsBoundedProfile M p}
  have hK : IsClosed K := isClosed_boundedProfiles M hM
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_boundedProfiles M hM)
  let : Nonempty K := nonempty_boundedProfiles M hM
  let μ' : ℕ → FiniteMeasure K := fun n => (μ n).comap Subtype.val
  have hμ' : ∀ n, (μ' n).mass ≤ C := fun n =>
    ((μ n).mass_comap_le Subtype.val).trans (hμ n)
  obtain ⟨ν', hν', φ, hφ, ht⟩ :=
    ProfileWeakCompactness.exists_finiteMeasure_subsequence C μ' hμ'
  refine ⟨ν'.map Subtype.val, ?_, map_subtype_support hK ν', φ, hφ, ?_⟩
  · exact (FiniteMeasure.mass_map_le measurable_subtype_coe.aemeasurable).trans hν'
  · have he : μ ∘ φ = (fun η : FiniteMeasure K => η.map (Subtype.val : K → Profile)) ∘
        (μ' ∘ φ) := by
      funext n
      exact (map_comap_subtype hK (μ (φ n)) (hs (φ n))).symm
    rw [he]
    exact (FiniteMeasure.continuous_map continuous_subtype_val).tendsto ν' |>.comp ht

theorem exists_full_ambient_profile_subsequence (M : ℝ) (hM : 0 ≤ M)
    (c : ℕ → ℝ) (hc : ∀ n, c n ∈ Set.Icc (0 : ℝ) 1)
    (p : ℕ → Profile) (hp : ∀ n, IsBoundedProfile M (p n))
    (C D : ℝ≥0) (μ ν : ℕ → FiniteMeasure Profile)
    (hμ : ∀ n, (μ n).mass ≤ C) (hν : ∀ n, (ν n).mass ≤ D)
    (hsμ : ∀ n, μ n {p | IsBoundedProfile M p}ᶜ = 0)
    (hsν : ∀ n, ν n {p | IsBoundedProfile M p}ᶜ = 0) :
    ∃ c₀ ∈ Set.Icc (0 : ℝ) 1, ∃ P : Profile, IsBoundedProfile M P ∧
      ∃ μ₀ ν₀ : FiniteMeasure Profile,
      μ₀.mass ≤ C ∧ ν₀.mass ≤ D ∧
      μ₀ {p | IsBoundedProfile M p}ᶜ = 0 ∧
      ν₀ {p | IsBoundedProfile M p}ᶜ = 0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (c ∘ φ) atTop (𝓝 c₀) ∧ Tendsto (p ∘ φ) atTop (𝓝 P) ∧
      Tendsto (μ ∘ φ) atTop (𝓝 μ₀) ∧ Tendsto (ν ∘ φ) atTop (𝓝 ν₀) := by
  let K := {p : Profile | IsBoundedProfile M p}
  have hK : IsClosed K := isClosed_boundedProfiles M hM
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_boundedProfiles M hM)
  let : Nonempty K := nonempty_boundedProfiles M hM
  let x : ℕ → Set.Icc (0 : ℝ) 1 × K := fun n => (⟨c n, hc n⟩, ⟨p n,hp n⟩)
  let μ' : ℕ → FiniteMeasure K := fun n => (μ n).comap Subtype.val
  let ν' : ℕ → FiniteMeasure K := fun n => (ν n).comap Subtype.val
  have hμ' : ∀ n, (μ' n).mass ≤ C := fun n =>
    ((μ n).mass_comap_le Subtype.val).trans (hμ n)
  have hν' : ∀ n, (ν' n).mass ≤ D := fun n =>
    ((ν n).mass_comap_le Subtype.val).trans (hν n)
  obtain ⟨a, μ₀, ν₀, hm, hn, φ, hφ, hx, hmt, hnt⟩ :=
    ProfileWeakCompactness.exists_simultaneous_subsequence x C D μ' ν' hμ' hν'
  refine ⟨a.1.val, a.1.property, a.2.val, a.2.property,
    μ₀.map Subtype.val, ν₀.map Subtype.val,
    (FiniteMeasure.mass_map_le measurable_subtype_coe.aemeasurable).trans hm,
    (FiniteMeasure.mass_map_le measurable_subtype_coe.aemeasurable).trans hn,
    map_subtype_support hK μ₀, map_subtype_support hK ν₀, φ, hφ, ?_, ?_, ?_, ?_⟩
  · exact (continuous_subtype_val.tendsto a.1).comp ((continuous_fst.tendsto a).comp hx)
  · exact (continuous_subtype_val.tendsto a.2).comp ((continuous_snd.tendsto a).comp hx)
  · have he : μ ∘ φ = (fun η : FiniteMeasure K => η.map (Subtype.val : K → Profile)) ∘
        (μ' ∘ φ) := by
      funext n
      exact (map_comap_subtype hK (μ (φ n)) (hsμ (φ n))).symm
    rw [he]
    exact (FiniteMeasure.continuous_map continuous_subtype_val).tendsto μ₀ |>.comp hmt
  · have he : ν ∘ φ = (fun η : FiniteMeasure K => η.map (Subtype.val : K → Profile)) ∘
        (ν' ∘ φ) := by
      funext n
      exact (map_comap_subtype hK (ν (φ n)) (hsν (φ n))).symm
    rw [he]
    exact (FiniteMeasure.continuous_map continuous_subtype_val).tendsto ν₀ |>.comp hnt

end Balanced.ProfileAmbientCompactness

end

end OAI
