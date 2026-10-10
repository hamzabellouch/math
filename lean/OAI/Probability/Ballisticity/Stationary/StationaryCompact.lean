import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace BoundedContinuousFunction
open scoped Topology
namespace DirectionalTransience.StationaryCompact

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] [MetrizableSpace Ω] [SecondCountableTopology Ω]

omit [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω] in
theorem invariant_of_weak_limit (T : Ω → Ω) (hT : Continuous T)
    (μs : ℕ → ProbabilityMeasure Ω) (μ : ProbabilityMeasure Ω)
    (hlim : Tendsto μs atTop (𝓝 μ))
    (hdefect : ∀ F : Ω →ᵇ ℝ,
      Tendsto (fun n => (∫ x, F (T x) ∂(μs n : Measure Ω)) -
        ∫ x, F x ∂(μs n : Measure Ω)) atTop (𝓝 0)) :
    MeasurePreserving T (μ : Measure Ω) (μ : Measure Ω) := by
  refine ⟨hT.measurable, ?_⟩
  let ν := μ.map T
  have heq : ν.toFiniteMeasure = μ.toFiniteMeasure := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro F
    have h₁ := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μs μ hlim hT)) F
    have h₂ := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) F
    have h₃ : Tendsto (fun n =>
        (∫ x, F (T x) ∂(μs n : Measure Ω)) - ∫ x, F x ∂(μs n : Measure Ω))
        atTop (𝓝 ((∫ x, F x ∂(ν : Measure Ω)) - ∫ x, F x ∂(μ : Measure Ω))) := by
      convert h₁.sub h₂ using 1
      ext n
      rw [ProbabilityMeasure.toMeasure_map,
        integral_map hT.measurable.aemeasurable F.continuous.aestronglyMeasurable]
    have hz := tendsto_nhds_unique h₃ (hdefect F)
    exact sub_eq_zero.mp hz
  exact congrArg FiniteMeasure.toMeasure heq

theorem exists_invariant_subsequence (T : Ω → Ω) (hT : Continuous T)
    (μs : ℕ → ProbabilityMeasure Ω)
    (hdefect : ∀ F : Ω →ᵇ ℝ,
      Tendsto (fun n => (∫ x, F (T x) ∂(μs n : Measure Ω)) -
        ∫ x, F x ∂(μs n : Measure Ω)) atTop (𝓝 0)) :
    ∃ μ : ProbabilityMeasure Ω, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) ∧
      MeasurePreserving T (μ : Measure Ω) (μ : Measure Ω) := by
  obtain ⟨μ, -, φ, hφ, hlim⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (ProbabilityMeasure Ω))).tendsto_subseq
      (fun n => Set.mem_univ (μs n))
  exact ⟨μ, φ, hφ, hlim, invariant_of_weak_limit T hT (μs ∘ φ) μ hlim
    (fun F => (hdefect F).comp hφ.tendsto_atTop)⟩

omit [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω]
  [T2Space Ω] [MetrizableSpace Ω] [SecondCountableTopology Ω] in
lemma episode_telescope (T : Ω → Ω) (F : Ω → ℝ) (x : Ω) (M : ℕ) :
    (∑ i ∈ Finset.range M, (F (T (T^[i] x)) - F (T^[i] x))) =
      F (T^[M] x) - F x := by
  simpa only [Function.iterate_succ_apply', Function.iterate_zero, id_eq] using
    Finset.sum_range_sub (fun i => F (T^[i] x)) M

omit [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [T2Space Ω]
  [MetrizableSpace Ω] [SecondCountableTopology Ω] in
lemma episode_boundary_bound (T : Ω → Ω) (F : Ω →ᵇ ℝ) (x : Ω) (M : ℕ) :
    |∑ i ∈ Finset.range M, (F (T (T^[i] x)) - F (T^[i] x))| ≤ 2*‖F‖ := by
  rw [episode_telescope]
  exact (abs_sub _ _).trans (by
    have h₁ := F.norm_coe_le_norm (T^[M] x)
    have h₂ := F.norm_coe_le_norm x
    change |F (T^[M] x)| ≤ ‖F‖ at h₁
    change |F x| ≤ ‖F‖ at h₂
    linarith)

end DirectionalTransience.StationaryCompact

end

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace BoundedContinuousFunction
open scoped ENNReal Topology
namespace DirectionalTransience.StationaryCompact

variable {X Y : Type*} [MeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

noncomputable def episodeOccupationRaw (N : ℕ) (μ : Measure X)
    (A : X → Y) (M : X → ℕ) (T : Y → Y) : Measure Y :=
  ∑ i ∈ Finset.range N, (μ.restrict {x | i < M x}).map (fun x => T^[i] (A x))

instance episodeOccupationRaw_finite (N : ℕ) (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → Y) (M : X → ℕ) (T : Y → Y) :
    IsFiniteMeasure (episodeOccupationRaw N μ A M T) := by
  unfold episodeOccupationRaw
  infer_instance

lemma sum_indicator_range (N M : ℕ) (hM : M ≤ N) (G : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, (if i < M then G i else 0)) = ∑ i ∈ Finset.range M, G i := by
  have he : (Finset.range N).filter (fun i => i < M) = Finset.range M := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [←Finset.sum_filter, he]

lemma episodeOccupationRaw_integral (N : ℕ) (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → Y) (hA : Measurable A) (M : X → ℕ) (hM : Measurable M)
    (hMN : ∀ x, M x ≤ N) (T : Y → Y) (hT : Measurable T)
    (F : Y →ᵇ ℝ) :
    (∫ y, F y ∂episodeOccupationRaw N μ A M T) =
      ∫ x, ∑ i ∈ Finset.range (M x), F (T^[i] (A x)) ∂μ := by
  have hi (i : ℕ) : Integrable (fun x => F (T^[i] (A x))) μ := by
    apply (integrable_const ‖F‖).mono' ((F.continuous.measurable.comp
      ((hT.iterate i).comp hA)).aestronglyMeasurable)
    exact Eventually.of_forall fun x => F.norm_coe_le_norm _
  have hm (i : ℕ) : MeasurableSet {x | i < M x} := measurableSet_lt measurable_const hM
  rw [episodeOccupationRaw]
  rw [integral_finsetSum_measure (fun i _ =>
    BoundedContinuousFunction.integrable ((μ.restrict {x | i < M x}).map
      (fun x => T^[i] (A x))) F)]
  calc (∑ i ∈ Finset.range N, ∫ y, F y ∂(μ.restrict {x | i < M x}).map
        (fun x => T^[i] (A x)))
      = ∑ i ∈ Finset.range N, ∫ x,
          Set.indicator {x | i < M x} (fun x => F (T^[i] (A x))) x ∂μ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_indicator (hm i)]
          exact integral_map ((hT.iterate i).comp hA).aemeasurable
            F.continuous.aestronglyMeasurable
    _ = ∫ x, ∑ i ∈ Finset.range N,
          Set.indicator {x | i < M x} (fun x => F (T^[i] (A x))) x ∂μ :=
          (integral_finsetSum _ (fun i _ => (hi i).indicator (hm i))).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [Set.indicator_apply,Set.mem_ofPred_eq]
        exact sum_indicator_range N (M x) (hMN x) _

lemma episodeOccupationRaw_mass (N : ℕ) (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → Y) (hA : Measurable A) (M : X → ℕ) (hM : Measurable M)
    (hMN : ∀ x, M x ≤ N) (T : Y → Y) (hT : Measurable T) :
    (episodeOccupationRaw N μ A M T).real Set.univ = ∫ x, (M x : ℝ) ∂μ := by
  simpa using episodeOccupationRaw_integral N μ A hA M hM hMN T hT
    (BoundedContinuousFunction.const Y (1:ℝ))

noncomputable def episodeOccupation [Nonempty Y] (N : ℕ) (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → Y) (M : X → ℕ) (T : Y → Y) : ProbabilityMeasure Y :=
  FiniteMeasure.normalize (⟨episodeOccupationRaw N μ A M T, inferInstance⟩ : FiniteMeasure Y)

lemma episodeOccupation_integral [Nonempty Y] (N : ℕ) (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → Y) (hA : Measurable A) (M : X → ℕ) (hM : Measurable M)
    (hMN : ∀ x, M x ≤ N) (hpos : 0 < ∫ x, (M x:ℝ) ∂μ)
    (T : Y → Y) (hT : Measurable T) (F : Y →ᵇ ℝ) :
    (∫ y, F y ∂(episodeOccupation N μ A M T : Measure Y)) =
      (∫ x, (M x:ℝ) ∂μ)⁻¹ * ∫ x, ∑ i ∈ Finset.range (M x), F (T^[i] (A x)) ∂μ := by
  let ρ : FiniteMeasure Y := ⟨episodeOccupationRaw N μ A M T,inferInstance⟩
  have hn : ρ ≠ 0 := by
    intro hz
    have hh : (episodeOccupationRaw N μ A M T).real Set.univ = 0 := by
      change (ρ : Measure Y).real Set.univ = 0
      rw [hz]
      simp
    rw [episodeOccupationRaw_mass N μ A hA M hM hMN T hT] at hh
    linarith
  change (∫ y, F y ∂(ρ.normalize : Measure Y)) = _
  rw [←ρ.average_eq_integral_normalize hn,average,integral_smul_measure]
  change ((episodeOccupationRaw N μ A M T) Set.univ)⁻¹.toReal *
      (∫ y, F y ∂episodeOccupationRaw N μ A M T) = _
  rw [ENNReal.toReal_inv,←Measure.real,
    episodeOccupationRaw_mass N μ A hA M hM hMN T hT,
    episodeOccupationRaw_integral N μ A hA M hM hMN T hT]

lemma episode_sum_integrable (N : ℕ) (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → Y) (hA : Measurable A) (M : X → ℕ) (hM : Measurable M)
    (hMN : ∀ x, M x ≤ N) (T : Y → Y) (hT : Measurable T)
    (F : Y →ᵇ ℝ) :
    Integrable (fun x => ∑ i ∈ Finset.range (M x), F (T^[i] (A x))) μ := by
  have hi (i : ℕ) : Integrable (fun x => F (T^[i] (A x))) μ := by
    apply (integrable_const ‖F‖).mono' ((F.continuous.measurable.comp
      ((hT.iterate i).comp hA)).aestronglyMeasurable)
    exact Eventually.of_forall fun x => F.norm_coe_le_norm _
  have hm (i : ℕ) : MeasurableSet {x | i < M x} := measurableSet_lt measurable_const hM
  have hh := integrable_finsetSum (Finset.range N) (fun i _ => (hi i).indicator (hm i))
  apply hh.congr
  exact Eventually.of_forall fun x => by
    change (∑ i ∈ Finset.range N, Set.indicator {x | i < M x}
      (fun x => F (T^[i] (A x))) x) = _
    simp only [Set.indicator_apply,Set.mem_ofPred_eq]
    exact sum_indicator_range N (M x) (hMN x) _

lemma episodeOccupation_defect [Nonempty Y] [CompactSpace Y] [T2Space Y]
    [MetrizableSpace Y] (N : ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (A : X → Y) (hA : Measurable A) (M : X → ℕ) (hM : Measurable M)
    (hMN : ∀ x, M x ≤ N) (hpos : 0 < ∫ x, (M x:ℝ) ∂μ)
    (T : Y → Y) (hT : Continuous T) (F : Y →ᵇ ℝ) :
    |(∫ y, F (T y) ∂(episodeOccupation N μ A M T : Measure Y)) -
      ∫ y, F y ∂(episodeOccupation N μ A M T : Measure Y)| ≤
      2*‖F‖ / (∫ x, (M x:ℝ) ∂μ) := by
  let G : Y →ᵇ ℝ := F.compContinuous ⟨T,hT⟩
  change |(∫ y, G y ∂(episodeOccupation N μ A M T : Measure Y)) -
      ∫ y, F y ∂(episodeOccupation N μ A M T : Measure Y)| ≤ _
  rw [episodeOccupation_integral N μ A hA M hM hMN hpos T hT.measurable G,
    episodeOccupation_integral N μ A hA M hM hMN hpos T hT.measurable F,
    ←mul_sub,←integral_sub (episode_sum_integrable N μ A hA M hM hMN T hT.measurable G)
      (episode_sum_integrable N μ A hA M hM hMN T hT.measurable F)]
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr hpos.le),div_eq_inv_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hpos.le)
  have hh := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun x => (∑ i ∈ Finset.range (M x), G (T^[i] (A x))) -
      ∑ i ∈ Finset.range (M x), F (T^[i] (A x)))
    (C := 2*‖F‖) (Eventually.of_forall fun x => by
      rw [←Finset.sum_sub_distrib]
      exact episode_boundary_bound T F (A x) (M x))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

theorem episodeOccupation_stationary_limit [SecondCountableTopology Y]
    [Nonempty Y] [CompactSpace Y] [T2Space Y]
    [MetrizableSpace Y] (Ns : ℕ → ℕ) (μs : ℕ → Measure X)
    [∀ n, IsProbabilityMeasure (μs n)]
    (As : ℕ → X → Y) (hAs : ∀ n, Measurable (As n))
    (Ms : ℕ → X → ℕ) (hMs : ∀ n, Measurable (Ms n))
    (hMN : ∀ n x, Ms n x ≤ Ns n)
    (hpos : ∀ n, 0 < ∫ x, (Ms n x:ℝ) ∂μs n)
    (hcount : Tendsto (fun n => ∫ x, (Ms n x:ℝ) ∂μs n) atTop atTop)
    (T : Y → Y) (hT : Continuous T) :
    ∃ μ : ProbabilityMeasure Y, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun n => episodeOccupation (Ns (φ n)) (μs (φ n)) (As (φ n)) (Ms (φ n)) T)
        atTop (𝓝 μ) ∧ MeasurePreserving T (μ : Measure Y) (μ : Measure Y) := by
  apply exists_invariant_subsequence T hT
    (fun n => episodeOccupation (Ns n) (μs n) (As n) (Ms n) T)
  intro F
  apply squeeze_zero_norm (fun n =>
    episodeOccupation_defect (Ns n) (μs n) (As n) (hAs n) (Ms n) (hMs n)
      (hMN n) (hpos n) T hT F)
  exact tendsto_const_nhds.div_atTop hcount

end DirectionalTransience.StationaryCompact

end

end OAI
