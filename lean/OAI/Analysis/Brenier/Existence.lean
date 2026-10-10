import OAI.Analysis.Brenier.AffineOptimality
import OAI.Analysis.Brenier.MapLimits
import OAI.Analysis.Brenier.PotentialLimits
import OAI.Analysis.Brenier.PrescribedCells
import OAI.Analysis.Brenier.Quantization

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal RealInnerProductSpace

namespace Problem358

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Existence and uniqueness among all quadratic transport plans for an arbitrary
strictly positive finite atomic target, with the exact uniform source definition.
The proof constructs the cell masses variationally rather than assuming them. -/
theorem exists_unique_optimal_map_uniform_atomic
    (K : Set (E d)) [IsProbabilityMeasure (uniformMeasure K)]
    (hK : IsCompact K) (y : ι → E d) (hinj : Function.Injective y)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) :
    ∃ T : E d → E d,
      IsUniqueQuadraticOptimalMap (uniformMeasure K)
        (∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i)) T := by
  obtain ⟨c, k, hc, hk, hmax, hmass⟩ :=
    MaxPotential.exists_prescribed_cell_masses_uniform K hK y hinj m hm hsum
  have hy : Measurable y := measurable_of_countable y
  have hT : Measurable (fun x => y (k x)) := hy.comp hk
  have hweights : ∀ i, uniformMeasure K (k ⁻¹' {i}) = ENNReal.ofReal (m i) := by
    intro i
    have hi : (uniformMeasure K).real (k ⁻¹' {i}) = m i := hmass i
    rw [← hi]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hpush := map_finite_selector_of_masses (uniformMeasure K) k hk y
    (fun i => ENNReal.ofReal (m i)) hweights
  have hopt := isUniqueQuadraticOptimalMap_uniform_of_finite_affine K hK y c hinj hT
    (Filter.Eventually.of_forall (fun x => ⟨k x, rfl, hmax x⟩))
  exact ⟨fun x => y (k x), hpush ▸ hopt⟩

/-- The finite-target existence theorem in a presentation-free form. -/
theorem exists_unique_optimal_map_uniform_finite_supported
    (K : Set (E d)) (hK : IsCompact K) (hinterior : (interior K).Nonempty)
    (μ : Measure (E d)) [IsProbabilityMeasure μ]
    {F : Set (E d)} (hF : F.Finite) (hμ : IsSupported μ F) :
    ∃ T : E d → E d, IsUniqueQuadraticOptimalMap (uniformMeasure K) μ T := by
  let : IsProbabilityMeasure (uniformMeasure K) := UniformSource.probability hK hinterior
  obtain ⟨n, hn, y, m, hy, _, hm, hsum, hrepr⟩ :=
    exists_positive_finite_atomic_presentation hF hμ
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨T, hT⟩ := exists_unique_optimal_map_uniform_atomic K hK y hy m hm hsum
  exact ⟨T, hrepr.symm ▸ hT⟩

end Problem358

namespace Problem358

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Finite-target existence together with a globally convex normalized Lipschitz
potential and its pointwise supporting-slope inequality. -/
theorem exists_uniform_atomic_map_and_potential
    (K : Set (E d)) [IsProbabilityMeasure (uniformMeasure K)]
    (hK : IsCompact K) (y : ι → E d) (hinj : Function.Injective y)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (L : NNReal) (hL : ∀ i, ‖y i‖ ≤ L) (x₀ : E d) :
    ∃ (u : E d → ℝ) (T : E d → E d),
      IsUniqueQuadraticOptimalMap (uniformMeasure K)
        (∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i)) T ∧
      ConvexOn ℝ Set.univ u ∧ LipschitzWith L u ∧ u x₀ = 0 ∧
      (∀ x, T x ∈ Set.range y) ∧
      ∀ x z, u x + ⟪T x, z - x⟫ ≤ u z := by
  obtain ⟨c, k, hc, hk, hmax, hmass⟩ :=
    MaxPotential.exists_prescribed_cell_masses_uniform K hK y hinj m hm hsum
  let T : E d → E d := fun x => y (k x)
  let u : E d → ℝ := fun x => MaxPotential.potential y c x - MaxPotential.potential y c x₀
  have hy : Measurable y := measurable_of_countable y
  have hT : Measurable T := hy.comp hk
  have hweights : ∀ i, uniformMeasure K (k ⁻¹' {i}) = ENNReal.ofReal (m i) := by
    intro i
    have hi : (uniformMeasure K).real (k ⁻¹' {i}) = m i := hmass i
    rw [← hi]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hpush := map_finite_selector_of_masses (uniformMeasure K) k hk y
    (fun i => ENNReal.ofReal (m i)) hweights
  have hopt := isUniqueQuadraticOptimalMap_uniform_of_finite_affine K hK y c hinj hT
    (Filter.Eventually.of_forall (fun x => ⟨k x, rfl, hmax x⟩))
  refine ⟨u, T, hpush ▸ hopt, ?_, ?_, ?_, ?_, ?_⟩
  · exact (MaxPotential.convexOn_potential y c).sub
      (concaveOn_const _ convex_univ)
  · apply LipschitzWith.of_dist_le_mul
    intro x z
    simpa only [u, Real.dist_eq, sub_sub_sub_cancel_right] using
      (MaxPotential.lipschitzWith_potential y c L hL).dist_le_mul x z
  · simp [u]
  · intro x
    exact ⟨k x, rfl⟩
  · intro x z
    have h := MaxPotential.supporting_inequality y c x z (k x) (hmax x)
    dsimp [u, T]
    rw [real_inner_comm] at h
    linarith

/-- Presentation-free finite-source data for compactness/approximation arguments. -/
theorem exists_uniform_finite_map_and_potential
    (K : Set (E d)) (hK : IsCompact K) (hinterior : (interior K).Nonempty)
    (μ : Measure (E d)) [IsProbabilityMeasure μ]
    {F Y : Set (E d)} (hF : F.Finite) (hFY : F ⊆ Y) (hμ : IsSupported μ F)
    (L : NNReal) (hL : ∀ z ∈ Y, ‖z‖ ≤ L) (x₀ : E d) :
    ∃ (u : E d → ℝ) (T : E d → E d),
      IsUniqueQuadraticOptimalMap (uniformMeasure K) μ T ∧
      ConvexOn ℝ Set.univ u ∧ LipschitzWith L u ∧ u x₀ = 0 ∧
      (∀ x, T x ∈ Y) ∧ ∀ x z, u x + ⟪T x, z - x⟫ ≤ u z := by
  let : IsProbabilityMeasure (uniformMeasure K) := UniformSource.probability hK hinterior
  obtain ⟨n, hn, y, m, hy, hyF, hm, hsum, hrepr⟩ :=
    exists_positive_finite_atomic_presentation hF hμ
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨u, T, hT, hu, hLip, hnorm, hrange, hsupport⟩ :=
    exists_uniform_atomic_map_and_potential K hK y hy m hm hsum L
      (fun i => hL (y i) (hFY (hyF i))) x₀
  refine ⟨u, T, hrepr.symm ▸ hT, hu, hLip, hnorm, ?_, hsupport⟩
  intro x
  obtain ⟨i, hi⟩ := hrange x
  rw [← hi]
  exact hFY (hyF i)

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal

namespace Problem358

/-- Passing normalized convex supporting potentials and their maps to the limit gives a
unique optimal map with the prescribed target law. No stability estimate is required here. -/
theorem exists_unique_optimal_map_of_approximating_potentials
    {d : ℕ} {K Y : Set (E d)} {μ : Measure (E d)}
    [IsFiniteMeasure (uniformMeasure K)] [IsFiniteMeasure μ]
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hY : IsCompact Y)
    (hμ : IsSupported μ Y) (x₀ : E d) (hx₀ : x₀ ∈ K)
    (uₙ : ℕ → E d → ℝ) (Tₙ Qₙ : ℕ → E d → E d) (L : ℝ≥0)
    (hLip : ∀ n, LipschitzOnWith L (uₙ n) K)
    (hconv : ∀ n, ConvexOn ℝ K (uₙ n))
    (hnormal : ∀ n, uₙ n x₀ = 0)
    (hTmeas : ∀ n, Measurable (Tₙ n)) (hQmeas : ∀ n, Measurable (Qₙ n))
    (hmem : ∀ n, ∀ᵐ x ∂uniformMeasure K, Tₙ n x ∈ Y)
    (hs : ∀ n, ∀ᵐ x ∂uniformMeasure K, ∀ z ∈ K,
      uₙ n x + inner ℝ (Tₙ n x) (z - x) ≤ uₙ n z)
    (hQlim : ∀ᵐ y ∂μ, Tendsto (fun n => Qₙ n y) atTop (𝓝 y))
    (hpush : ∀ n, Measure.map (Tₙ n) (uniformMeasure K) = Measure.map (Qₙ n) μ) :
    ∃ T : E d → E d, IsUniqueQuadraticOptimalMap (uniformMeasure K) μ T := by
  obtain ⟨u, T, φ, hφ, _, huLip, _, _, hT, hTlim, _, hsupport⟩ :=
    exists_potential_and_map_limit hK hKconv hY x₀ hx₀ uₙ Tₙ L
      hLip hconv hnormal hTmeas hmem hs
  have hQlim' : ∀ᵐ y ∂μ, Tendsto (fun n => Qₙ (φ n) y) atTop (𝓝 y) := by
    filter_upwards [hQlim] with y hy
    exact hy.comp hφ.tendsto_atTop
  have hpushT : Measure.map T (uniformMeasure K) = μ :=
    map_eq_of_ae_limits (fun n => hTmeas (φ n)) hT (fun n => hQmeas (φ n))
      hTlim hQlim' (fun n => hpush (φ n))
  refine ⟨T, isUniqueQuadraticOptimalMap_uniform_of_supporting_potential
    hK ⟨x₀, hx₀⟩ hKconv hY hμ huLip hT hpushT ?_⟩
  filter_upwards [hsupport] with x hx
  intro z hz
  simpa only [real_inner_comm] using hx z hz

/-- Reduction of general optimal-map existence to a uniformly Lipschitz convex-potential
construction for finite-range quantizations of the target. -/
theorem exists_unique_optimal_map_of_simpleFunc_potentials
    {d : ℕ} {K Y : Set (E d)} {μ : Measure (E d)}
    [IsFiniteMeasure (uniformMeasure K)] [IsFiniteMeasure μ]
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hY : IsCompact Y) (hYne : Y.Nonempty)
    (hμ : IsSupported μ Y) (x₀ : E d) (hx₀ : x₀ ∈ K) (L : ℝ≥0)
    (hfinite : ∀ q : SimpleFunc (E d) (E d), (∀ x, q x ∈ Y) →
      ∃ (u : E d → ℝ) (T : E d → E d), LipschitzOnWith L u K ∧
        ConvexOn ℝ K u ∧ u x₀ = 0 ∧ Measurable T ∧
        (∀ᵐ x ∂uniformMeasure K, T x ∈ Y) ∧
        (∀ᵐ x ∂uniformMeasure K, ∀ z ∈ K, u x + inner ℝ (T x) (z - x) ≤ u z) ∧
        Measure.map T (uniformMeasure K) = Measure.map q μ) :
    ∃ T : E d → E d, IsUniqueQuadraticOptimalMap (uniformMeasure K) μ T := by
  classical
  have hq : ∀ n : ℕ, ∃ q : SimpleFunc (E d) (E d), (∀ x, q x ∈ Y) ∧
      ∀ x ∈ Y, dist (q x) x < (1 : ℝ) / ((n : ℝ) + 1) := by
    intro n
    exact exists_compact_quantizer hY hYne (by positivity)
  choose q hqY hqdist using hq
  choose u T hLip hconv hnormal hTmeas hmem hs hpush using
    (fun n => hfinite (q n) (hqY n))
  apply exists_unique_optimal_map_of_approximating_potentials hK hKconv hY hμ
    x₀ hx₀ u T (fun n => q n) L hLip hconv hnormal hTmeas
    (fun n => (q n).measurable) hmem hs _ hpush
  filter_upwards [ae_iff.mpr hμ] with y hy
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun n => dist_nonneg) (fun n => (hqdist n y hy).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- General Brenier existence and uniqueness among all quadratic transport plans for
uniform compact convex sources and arbitrary compactly supported probability targets. -/
theorem exists_unique_optimal_map_uniform_compact
    {d : ℕ} {K Y : Set (E d)}
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hInterior : (interior K).Nonempty)
    (hY : IsCompact Y) (hYne : Y.Nonempty)
    (μ : Measure (E d)) [IsProbabilityMeasure μ] (hμ : IsSupported μ Y) :
    ∃ T : E d → E d, IsUniqueQuadraticOptimalMap (uniformMeasure K) μ T := by
  let : IsProbabilityMeasure (uniformMeasure K) := UniformSource.probability hK hInterior
  obtain ⟨x₀, hx₀⟩ := hInterior.mono interior_subset
  obtain ⟨R, hR⟩ := hY.isBounded.exists_norm_le
  let L : ℝ≥0 := ⟨max R 0, le_max_right _ _⟩
  have hL : ∀ y ∈ Y, ‖y‖ ≤ L := fun y hy => (hR y hy).trans (le_max_left _ _)
  apply exists_unique_optimal_map_of_simpleFunc_potentials hK hKconv hY hYne hμ x₀ hx₀ L
  intro q hqY
  let : IsProbabilityMeasure (Measure.map q μ) :=
    (Measure.isProbabilityMeasure_map_iff q.measurable.aemeasurable).mpr inferInstance
  have hFY : Set.range q ⊆ Y := by
    rintro y ⟨x, rfl⟩
    exact hqY x
  obtain ⟨u, T, hopt, hu, hLip, hnormal, hTY, hsupport⟩ :=
    exists_uniform_finite_map_and_potential K hK hInterior (Measure.map q μ)
      q.finite_range hFY (simpleFunc_map_finite_support μ q).2 L hL x₀
  exact ⟨u, T, hLip.lipschitzOnWith, hu.subset (Set.subset_univ K) hKconv,
    hnormal, hopt.1.1, ae_of_all _ hTY,
    ae_of_all _ (fun x z _ => hsupport x z), hopt.1.2.1⟩

end Problem358

end

end OAI
