import OAI.Combinatorics.BalancedRyser.Profiles.ProfileCompactness
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileEmpiricalSupport
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileMarginalContinuity

namespace OAI

noncomputable section
namespace Balanced.ProfileShrinkingExceptions
open Filter Topology TopologicalSpace MeasureTheory
open scoped NNReal BoundedContinuousFunction

theorem integral_le_threshold_mass
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : FiniteMeasure E) (g : E →ᵇ ℝ) (ε C : ℝ)
    (hε : 0 ≤ ε) (hm : (μ : Measure E).real Set.univ ≤ C)
    (he : (μ : Measure E).real {x | ε ≤ g x} ≤ ε) :
    (∫ x, g x ∂μ.toMeasure) ≤ ε * (C + ‖g‖) := by
  let A := {x | ε ≤ g x}
  have hA : MeasurableSet A := (isClosed_le continuous_const g.continuous).measurableSet
  have hp (x : E) : g x ≤ ε + A.indicator (fun _ => ‖g‖) x := by
    have hb : g x ≤ ‖g‖ := (le_abs_self _).trans (g.norm_coe_le_norm x)
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx]
      linarith
    · have hlt : g x < ε := lt_of_not_ge hx
      simp only [Set.indicator_of_notMem hx, add_zero]
      exact hlt.le
  have hi := integral_mono (g.integrable μ.toMeasure)
    ((integrable_const ε).add ((integrable_const ‖g‖).indicator hA)) hp
  simp only [Pi.add_apply] at hi
  rw [integral_add (integrable_const ε) ((integrable_const ‖g‖).indicator hA),
    integral_const, integral_indicator_const _ hA] at hi
  simp only [smul_eq_mul] at hi
  have hm' := mul_le_mul_of_nonneg_right hm hε
  have he' := mul_le_mul_of_nonneg_right he (norm_nonneg g)
  dsimp [A] at hi
  simp only [FiniteMeasure.measureReal_eq_coe_coeFn] at hm' he'
  nlinarith

theorem ae_eq_zero_of_shrinking_exceptions
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : ℕ → FiniteMeasure E} {ν : FiniteMeasure E}
    (ht : Tendsto μ atTop (𝓝 ν)) (g : E →ᵇ ℝ) (hg : ∀ x, 0 ≤ g x)
    (C : ℝ) (hm : ∀ n, (μ n : Measure E).real Set.univ ≤ C)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hεt : Tendsto ε atTop (𝓝 0))
    (he : ∀ n, (μ n : Measure E).real {x | ε n ≤ g x} ≤ ε n) :
    ∀ᵐ x ∂ν.toMeasure, g x = 0 := by
  have hint : Tendsto (fun n => ∫ x, g x ∂(μ n).toMeasure) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg hg)
      (fun n => integral_le_threshold_mass (μ n) g (ε n) C (hε n) (hm n) (he n))
    simpa using hεt.mul_const (C + ‖g‖)
  have hw := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp ht) g
  have hz : (∫ x, g x ∂ν.toMeasure) = 0 := tendsto_nhds_unique hw hint
  exact (integral_eq_zero_iff_of_nonneg hg (g.integrable ν.toMeasure)).mp hz

theorem tendsto_comap_subtype
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [NormalSpace E] {K : Set E} (hK : IsClosed K)
    {μ : ℕ → FiniteMeasure E} {ν : FiniteMeasure E}
    (hs : ∀ n, μ n Kᶜ = 0) (hsν : ν Kᶜ = 0)
    (ht : Tendsto μ atTop (𝓝 ν)) :
    Tendsto (fun n => (μ n).comap (Subtype.val : K → E)) atTop
      (𝓝 (ν.comap (Subtype.val : K → E))) := by
  have hi := FiniteMeasure.Topology.IsClosedEmbedding.isEmbedding_map_finiteMeasure
    (Subtype.val : K → E) (Topology.IsClosedEmbedding.subtypeVal hK)
  apply hi.tendsto_nhds_iff.mpr
  have he : (fun η : FiniteMeasure K => η.map (Subtype.val : K → E)) ∘
      (fun n => (μ n).comap (Subtype.val : K → E)) = μ := by
    funext n
    exact ProfileAmbientCompactness.map_comap_subtype hK (μ n) (hs n)
  rw [he, ProfileAmbientCompactness.map_comap_subtype hK ν hsν]
  exact ht

theorem ae_eq_const_of_shrinking_exceptions_on_compact
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [T2Space E] [PseudoMetrizableSpace E]
    {K : Set E} (hK : IsCompact K)
    {μ : ℕ → FiniteMeasure E} {ν : FiniteMeasure E}
    (hs : ∀ n, μ n Kᶜ = 0) (ht : Tendsto μ atTop (𝓝 ν))
    (f : E → ℝ) (hf : Measurable f)
    (hfc : Continuous (fun x : K => f x)) (a C : ℝ)
    (hm : ∀ n, (μ n : Measure E).real Set.univ ≤ C)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hεt : Tendsto ε atTop (𝓝 0))
    (he : ∀ n, (μ n : Measure E).real {x | ε n ≤ |f x - a|} ≤ ε n) :
    ∀ᵐ x ∂ν.toMeasure, f x = a := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let μ' : ℕ → FiniteMeasure K := fun n => (μ n).comap Subtype.val
  let ν' : FiniteMeasure K := ν.comap Subtype.val
  have hsν := ProfileAmbientCompactness.compact_support_of_tendsto hK hs ht
  have ht' : Tendsto μ' atTop (𝓝 ν') := tendsto_comap_subtype hK.isClosed hs hsν ht
  let g : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => |f x - a|, (hfc.sub continuous_const).abs⟩
  have hm' (n : ℕ) : (μ' n : Measure K).real Set.univ ≤ C := by
    apply le_trans _ (hm n)
    change ((μ' n).mass : ℝ) ≤ ((μ n).mass : ℝ)
    exact_mod_cast (μ n).mass_comap_le (Subtype.val : K → E)
  have he' (n : ℕ) : (μ' n : Measure K).real {x | ε n ≤ g x} ≤ ε n := by
    have hA : MeasurableSet {x : E | ε n ≤ |f x - a|} :=
      measurableSet_le measurable_const ((hf.sub measurable_const).abs)
    have heq : (μ' n : Measure K).real {x | ε n ≤ g x} =
        (μ n : Measure E).real {x | ε n ≤ |f x - a|} := by
      calc
        _ = ((μ' n).map (Subtype.val : K → E) : Measure E).real
            {x | ε n ≤ |f x - a|} := by
          simp only [FiniteMeasure.toMeasure_map, measureReal_def,
            Measure.map_apply measurable_subtype_coe hA]
          rfl
        _ = _ := congrArg (fun η : FiniteMeasure E =>
          (η : Measure E).real {x | ε n ≤ |f x - a|})
          (ProfileAmbientCompactness.map_comap_subtype hK.isClosed (μ n) (hs n))
    rw [heq]
    exact he n
  have hz := ae_eq_zero_of_shrinking_exceptions ht' g (fun _ => abs_nonneg _)
    C hm' ε hε hεt he'
  have hsub : ∀ᵐ (x : K) ∂ν'.toMeasure, f x = a := by
    filter_upwards [hz] with x hx
    exact sub_eq_zero.mp (abs_eq_zero.mp hx)
  have hmap : ∀ᵐ x ∂(ν'.map (Subtype.val : K → E)).toMeasure, f x = a := by
    change ∀ᵐ x ∂Measure.map (Subtype.val : K → E) ν'.toMeasure, f x = a
    exact (MeasurableEmbedding.subtype_coe hK.isClosed.measurableSet).ae_map_iff.mpr hsub
  have hmapν : ν'.map (Subtype.val : K → E) = ν :=
    ProfileAmbientCompactness.map_comap_subtype hK.isClosed ν hsν
  rwa [hmapν] at hmap

theorem integral_comap_subtype
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hK : IsClosed K) (μ : FiniteMeasure E) (hs : μ Kᶜ = 0)
    (f : E → ℝ) (hf : Measurable f) :
    (∫ x : K, f x ∂(μ.comap (Subtype.val : K → E)).toMeasure) =
      ∫ x, f x ∂μ.toMeasure := by
  have hm := congrArg FiniteMeasure.toMeasure
    (ProfileAmbientCompactness.map_comap_subtype hK μ hs)
  rw [FiniteMeasure.toMeasure_map] at hm
  rw [← hm, integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable]

theorem ae_eq_const_of_integral_tendsto_zero_on_compact
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [T2Space E] [PseudoMetrizableSpace E]
    {K : Set E} (hK : IsCompact K)
    {μ : ℕ → FiniteMeasure E} {ν : FiniteMeasure E}
    (hs : ∀ n, μ n Kᶜ = 0) (ht : Tendsto μ atTop (𝓝 ν))
    (f : E → ℝ) (hf : Measurable f)
    (hfc : Continuous (fun x : K => f x)) (a : ℝ)
    (hi : Tendsto (fun n => ∫ x, |f x - a| ∂(μ n).toMeasure) atTop (𝓝 0)) :
    ∀ᵐ x ∂ν.toMeasure, f x = a := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let μ' : ℕ → FiniteMeasure K := fun n => (μ n).comap Subtype.val
  let ν' : FiniteMeasure K := ν.comap Subtype.val
  have hsν := ProfileAmbientCompactness.compact_support_of_tendsto hK hs ht
  have ht' : Tendsto μ' atTop (𝓝 ν') := tendsto_comap_subtype hK.isClosed hs hsν ht
  let g : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => |f x - a|, (hfc.sub continuous_const).abs⟩
  have hi' : Tendsto (fun n => ∫ x, g x ∂(μ' n).toMeasure) atTop (𝓝 0) := by
    have he (n : ℕ) : (∫ x, g x ∂(μ' n).toMeasure) =
        ∫ x, |f x - a| ∂(μ n).toMeasure :=
      integral_comap_subtype hK.isClosed (μ n) (hs n) (fun x => |f x - a|)
        ((hf.sub measurable_const).abs)
    simpa only [he] using hi
  have hw := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp ht') g
  have hz : (∫ x, g x ∂ν'.toMeasure) = 0 := tendsto_nhds_unique hw hi'
  have hzero := (integral_eq_zero_iff_of_nonneg (fun (x : K) => abs_nonneg (f x - a))
    (g.integrable ν'.toMeasure)).mp hz
  have hsub : ∀ᵐ (x : K) ∂ν'.toMeasure, f x = a := by
    filter_upwards [hzero] with x hx
    exact sub_eq_zero.mp (abs_eq_zero.mp hx)
  have hmap : ∀ᵐ x ∂(ν'.map (Subtype.val : K → E)).toMeasure, f x = a := by
    change ∀ᵐ x ∂Measure.map (Subtype.val : K → E) ν'.toMeasure, f x = a
    exact (MeasurableEmbedding.subtype_coe hK.isClosed.measurableSet).ae_map_iff.mpr hsub
  have hmapν : ν'.map (Subtype.val : K → E) = ν :=
    ProfileAmbientCompactness.map_comap_subtype hK.isClosed ν hsν
  rwa [hmapν] at hmap

theorem profileSequenceLimit_row_sum_eq_of_integral_tendsto_zero
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) (a : ℝ)
    (hi : Tendsto (fun n => ∫ x, |(∑' j : ℕ, x (0,j)) - a|
      ∂(empiricalProfileMeasure (D n) (C n) (C n)).toMeasure) atTop (𝓝 0)) :
    ∀ᵐ x ∂νC.toMeasure, (∑' j : ℕ, x (0,j)) = a := by
  apply ae_eq_const_of_integral_tendsto_zero_on_compact
    (ProfileAmbientCompactness.isCompact_boundedProfiles (2 * (k : ℝ) + 4) (by positivity))
    (fun n => ProfileEmpiricalSupport.admissible_empirical_bounded_support
      k (D n) (C n) (C n) (hpair n).1 (hpair n).2.2) ht.2.2.2
    (fun x : Profile => ∑' j : ℕ, x (0,j))
    (ProfileContinuity.measurable_profile_row_sum 0)
    (ProfileContinuity.continuous_boundedProfile_row_sum (2 * (k : ℝ) + 4) 0) a hi

end Balanced.ProfileShrinkingExceptions

end

end OAI
