import OAI.Analysis.Brenier.AffineCertificate
import OAI.Analysis.Brenier.AffineTies
import OAI.Analysis.Brenier.CompactMeasure
import OAI.Analysis.Brenier.Optimality

namespace OAI

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace Problem358

variable {d : ℕ} {ι : Type*} [Fintype ι]
  {ρ : Measure (E d)} {T : E d → E d}

/-- An active finite-affine selection takes values in the finite site set almost everywhere. -/
theorem finiteAffine_map_ae_mem_range [Nonempty ι] (y : ι → E d) (c : ι → ℝ)
    (hT : Measurable T)
    (hactive : ∀ᵐ x ∂ρ, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y c x i) :
    ∀ᵐ z ∂Measure.map T ρ, z ∈ Set.range y := by
  apply (ae_map_iff hT.aemeasurable (Set.finite_range y).measurableSet).mpr
  filter_upwards [hactive] with x hx
  obtain ⟨i, hi, _⟩ := hx
  exact ⟨i, hi.symm⟩

variable [Nonempty ι]

/-- The pointwise finite-affine dual estimate holds under every competing coupling. -/
theorem finiteAffine_coupling_dual_bound (y : ι → E d) (c : ι → ℝ)
    (hy : Function.Injective y) (hT : Measurable T)
    (hactive : ∀ᵐ x ∂ρ, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y c x i)
    {π : Measure (E d × E d)} (hπ : IsCoupling ρ (Measure.map T ρ) π) :
    ∀ᵐ p ∂π, FiniteAffine.sourceDual y c p.1 +
      FiniteAffine.targetDual y c p.2 ≤ ‖p.1 - p.2‖ ^ 2 := by
  have hrange : ∀ᵐ p ∂π, p.2 ∈ Set.range y := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hπ.2.2]
    exact finiteAffine_map_ae_mem_range y c hT hactive
  exact hrange.mono fun p hp => FiniteAffine.dual_le_cost_on_range y c hy p.1 p.2 hp

/-- A measurable active selection of distinct affine sites is quadratically optimal. -/
theorem isQuadraticOptimalMap_of_finite_affine
    [IsProbabilityMeasure ρ] (y : ι → E d) (c : ι → ℝ)
    (hy : Function.Injective y) (hT : Measurable T)
    (hsource : Integrable (FiniteAffine.sourceDual y c) ρ)
    (hactive : ∀ᵐ x ∂ρ, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y c x i) :
    IsQuadraticOptimalMap ρ (Measure.map T ρ) T := by
  let : IsProbabilityMeasure (Measure.map T ρ) := inferInstance
  apply isQuadraticOptimalMap_of_dual hT rfl hsource
    (FiniteAffine.integrable_targetDual y c (Measure.map T ρ))
  · intro π hπ
    exact finiteAffine_coupling_dual_bound y c hy hT hactive hπ
  · filter_upwards [hactive] with x hx
    obtain ⟨i, hi, hmax⟩ := hx
    rw [hi, FiniteAffine.targetDual_site y c hy i]
    exact (FiniteAffine.dual_eq_cost_of_maximizes y c x i hmax).symm

/-- Under an absolutely continuous source, saturation of the finite-affine certificate
    forces every competing plan onto the selected graph. -/
theorem finiteAffine_dual_eq_implies_graph_ae
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (hρ : ρ ≪ (volume : Measure (E d))) (hT : Measurable T)
    (hactive : ∀ᵐ x ∂ρ, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y c x i)
    {π : Measure (E d × E d)} (hπ : IsCoupling ρ (Measure.map T ρ) π) :
    ∀ᵐ p ∂π, FiniteAffine.sourceDual y c p.1 +
      FiniteAffine.targetDual y c p.2 = ‖p.1 - p.2‖ ^ 2 → p.2 = T p.1 := by
  have htie : ∀ᵐ x ∂ρ, ∀ i j,
      ⟪x, y i⟫ + c i = ⟪x, y j⟫ + c j → y i = y j :=
    hρ.ae_le (ae_affine_tie_implies_slopes_eq volume y c)
  have hfst : ∀ᵐ p ∂π, (∃ i, T p.1 = y i ∧ FiniteAffine.Maximizes y c p.1 i) ∧
      (∀ i j, ⟪p.1, y i⟫ + c i = ⟪p.1, y j⟫ + c j → y i = y j) := by
    have h := hactive.and htie
    rw [← hπ.2.1] at h
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have hsnd : ∀ᵐ p ∂π, p.2 ∈ Set.range y := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hπ.2.2]
    exact finiteAffine_map_ae_mem_range y c hT hactive
  filter_upwards [hfst, hsnd] with p hp hpy
  intro heq
  obtain ⟨i, hi, hmax⟩ := hp.1
  obtain ⟨j, hj⟩ := hpy
  have hjmax : FiniteAffine.Maximizes y c p.1 j := by
    apply (FiniteAffine.dual_eq_cost_on_range_iff y c hy p.1 j).mp
    simpa only [hj] using heq
  have hsites : y j = y i := hp.2 j i (le_antisymm (hmax j) (hjmax i))
  exact hj.symm.trans (hsites.trans hi.symm)

/-- Compact support makes the continuous source potential integrable. -/
theorem integrable_finiteAffine_sourceDual_of_compact
    [IsFiniteMeasure ρ] (y : ι → E d) (c : ι → ℝ)
    {K : Set (E d)} (hK : IsCompact K) (hρK : IsSupported ρ K) :
    Integrable (FiniteAffine.sourceDual y c) ρ := by
  have hae : ∀ᵐ x ∂ρ, x ∈ K := by
    rw [ae_iff]
    exact hρK
  have hi := ContinuousOn.integrableOn_compact hK
    (FiniteAffine.continuous_sourceDual y c).continuousOn (μ := ρ)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at hi

/-- The finite-affine construction gives uniqueness among all transport plans, not
    merely among maps, whenever the source is absolutely continuous. -/
theorem isUniqueQuadraticOptimalMap_of_finite_affine
    [IsProbabilityMeasure ρ] (y : ι → E d) (c : ι → ℝ)
    (hy : Function.Injective y) (hρ : ρ ≪ (volume : Measure (E d)))
    (hT : Measurable T) (hsource : Integrable (FiniteAffine.sourceDual y c) ρ)
    (hactive : ∀ᵐ x ∂ρ, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y c x i) :
    IsUniqueQuadraticOptimalMap ρ (Measure.map T ρ) T := by
  let : IsProbabilityMeasure (Measure.map T ρ) := inferInstance
  apply isUniqueQuadraticOptimalMap_of_dual hT rfl hsource
    (FiniteAffine.integrable_targetDual y c (Measure.map T ρ))
  · intro π hπ
    exact finiteAffine_coupling_dual_bound y c hy hT hactive hπ
  · filter_upwards [hactive] with x hx
    obtain ⟨i, hi, hmax⟩ := hx
    rw [hi, FiniteAffine.targetDual_site y c hy i]
    exact (FiniteAffine.dual_eq_cost_of_maximizes y c x i hmax).symm
  · intro π hπ
    exact finiteAffine_dual_eq_implies_graph_ae y c hy hρ hT hactive hπ

/-- Compactly supported absolutely continuous probabilities admit the finite-affine
    optimality certificate without auxiliary integrability assumptions. -/
theorem isUniqueQuadraticOptimalMap_of_finite_affine_of_compact
    [IsProbabilityMeasure ρ] (y : ι → E d) (c : ι → ℝ)
    (hy : Function.Injective y) (hρ : ρ ≪ (volume : Measure (E d)))
    {K : Set (E d)} (hK : IsCompact K) (hρK : IsSupported ρ K)
    (hT : Measurable T)
    (hactive : ∀ᵐ x ∂ρ, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y c x i) :
    IsUniqueQuadraticOptimalMap ρ (Measure.map T ρ) T :=
  isUniqueQuadraticOptimalMap_of_finite_affine y c hy hρ hT
    (integrable_finiteAffine_sourceDual_of_compact y c hK hρK) hactive

/-- Uniform compact-source specialization for the finite-affine maps used in sharpness. -/
theorem isUniqueQuadraticOptimalMap_uniform_of_finite_affine
    (K : Set (E d)) [IsProbabilityMeasure (uniformMeasure K)]
    (hK : IsCompact K) (y : ι → E d) (c : ι → ℝ)
    (hy : Function.Injective y) (hT : Measurable T)
    (hactive : ∀ᵐ x ∂uniformMeasure K,
      ∃ i, T x = y i ∧ FiniteAffine.Maximizes y c x i) :
    IsUniqueQuadraticOptimalMap (uniformMeasure K)
      (Measure.map T (uniformMeasure K)) T := by
  have hac : uniformMeasure K ≪ (volume : Measure (E d)) :=
    Measure.absolutelyContinuous_restrict.smul_left _
  have hs : IsSupported (uniformMeasure K) K := by
    simp [IsSupported, uniformMeasure, Measure.restrict_apply hK.measurableSet.compl]
  exact isUniqueQuadraticOptimalMap_of_finite_affine_of_compact y c hy hac hK hs hT hactive

end Problem358

namespace Problem358.FiniteAffine

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A measurable active-site map solves the quadratic transport problem to its law. -/
theorem isQuadraticOptimalMap_of_maximizes
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (ρ : Measure (E d)) [IsProbabilityMeasure ρ]
    {T : E d → E d} (hT : Measurable T)
    (hsource : Integrable (sourceDual y c) ρ)
    (hmax : ∀ᵐ x ∂ρ, ∃ i, T x = y i ∧ Maximizes y c x i) :
    IsQuadraticOptimalMap ρ (Measure.map T ρ) T := by
  have : IsProbabilityMeasure (Measure.map T ρ) := inferInstance
  have hrange : ∀ᵐ z ∂Measure.map T ρ, z ∈ Set.range y := by
    apply (ae_map_iff hT.aemeasurable (Set.finite_range y).measurableSet).mpr
    filter_upwards [hmax] with x hx
    obtain ⟨i, hi, _⟩ := hx
    exact ⟨i, hi.symm⟩
  apply isQuadraticOptimalMap_of_dual hT rfl hsource
    (integrable_targetDual y c (Measure.map T ρ))
  · intro π hπ
    have hrange' : ∀ᵐ z ∂Measure.map Prod.snd π, z ∈ Set.range y := hπ.2.2.symm ▸ hrange
    filter_upwards [ae_of_ae_map measurable_snd.aemeasurable hrange'] with p hp
    exact dual_le_cost_on_range y c hy p.1 p.2 hp
  · filter_upwards [hmax] with x hx
    obtain ⟨i, hi, hmi⟩ := hx
    rw [hi, targetDual_site y c hy]
    exact (dual_eq_cost_of_maximizes y c x i hmi).symm

/-- Compact support supplies the dual-potential integrability automatically. -/
theorem isQuadraticOptimalMap_of_maximizes_of_compact
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (ρ : Measure (E d)) [IsProbabilityMeasure ρ]
    {K : Set (E d)} (hK : IsCompact K) (hρ : IsSupported ρ K)
    {T : E d → E d} (hT : Measurable T)
    (hmax : ∀ᵐ x ∂ρ, ∃ i, T x = y i ∧ Maximizes y c x i) :
    IsQuadraticOptimalMap ρ (Measure.map T ρ) T :=
  isQuadraticOptimalMap_of_maximizes y c hy ρ hT
    (hρ.integrable_continuousOn hK (continuous_sourceDual y c).continuousOn) hmax

/-- No ties between distinct maximizing sites upgrades finite-affine optimality to plan uniqueness. -/
theorem isUniqueQuadraticOptimalMap_of_maximizes
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (ρ : Measure (E d)) [IsProbabilityMeasure ρ]
    {T : E d → E d} (hT : Measurable T)
    (hsource : Integrable (sourceDual y c) ρ)
    (hmax : ∀ᵐ x ∂ρ, ∃ i, T x = y i ∧ Maximizes y c x i)
    (hunique : ∀ᵐ x ∂ρ, ∀ i j, Maximizes y c x i →
      Maximizes y c x j → y i = y j) :
    IsUniqueQuadraticOptimalMap ρ (Measure.map T ρ) T := by
  have : IsProbabilityMeasure (Measure.map T ρ) := inferInstance
  have hrange : ∀ᵐ z ∂Measure.map T ρ, z ∈ Set.range y := by
    apply (ae_map_iff hT.aemeasurable (Set.finite_range y).measurableSet).mpr
    filter_upwards [hmax] with x hx
    obtain ⟨i, hi, _⟩ := hx
    exact ⟨i, hi.symm⟩
  apply isUniqueQuadraticOptimalMap_of_dual hT rfl hsource
    (integrable_targetDual y c (Measure.map T ρ))
  · intro π hπ
    have hrange' : ∀ᵐ z ∂Measure.map Prod.snd π, z ∈ Set.range y := hπ.2.2.symm ▸ hrange
    filter_upwards [ae_of_ae_map measurable_snd.aemeasurable hrange'] with p hp
    exact dual_le_cost_on_range y c hy p.1 p.2 hp
  · filter_upwards [hmax] with x hx
    obtain ⟨i, hi, hmi⟩ := hx
    rw [hi, targetDual_site y c hy]
    exact (dual_eq_cost_of_maximizes y c x i hmi).symm
  · intro π hπ
    have hrange' : ∀ᵐ z ∂Measure.map Prod.snd π, z ∈ Set.range y := hπ.2.2.symm ▸ hrange
    have hmax' : ∀ᵐ x ∂Measure.map Prod.fst π,
        ∃ i, T x = y i ∧ Maximizes y c x i := hπ.2.1.symm ▸ hmax
    have huniq' : ∀ᵐ x ∂Measure.map Prod.fst π,
        ∀ i j, Maximizes y c x i → Maximizes y c x j → y i = y j :=
      hπ.2.1.symm ▸ hunique
    filter_upwards [ae_of_ae_map measurable_snd.aemeasurable hrange',
      ae_of_ae_map measurable_fst.aemeasurable hmax',
      ae_of_ae_map measurable_fst.aemeasurable huniq'] with p hp hm hu
    intro heq
    obtain ⟨j, hj⟩ := hp
    obtain ⟨i, hi, hmi⟩ := hm
    have hmj : Maximizes y c p.1 j := by
      apply (dual_eq_cost_on_range_iff y c hy p.1 j).mp
      simpa only [hj] using heq
    exact hj.symm.trans ((hu j i hmj hmi).trans hi.symm)

/-- The compact-source form of the finite-affine unique-optimality criterion. -/
theorem isUniqueQuadraticOptimalMap_of_maximizes_of_compact
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (ρ : Measure (E d)) [IsProbabilityMeasure ρ]
    {K : Set (E d)} (hK : IsCompact K) (hρ : IsSupported ρ K)
    {T : E d → E d} (hT : Measurable T)
    (hmax : ∀ᵐ x ∂ρ, ∃ i, T x = y i ∧ Maximizes y c x i)
    (hunique : ∀ᵐ x ∂ρ, ∀ i j, Maximizes y c x i →
      Maximizes y c x j → y i = y j) :
    IsUniqueQuadraticOptimalMap ρ (Measure.map T ρ) T :=
  isUniqueQuadraticOptimalMap_of_maximizes y c hy ρ hT
    (hρ.integrable_continuousOn hK (continuous_sourceDual y c).continuousOn) hmax hunique

/-- For an absolutely continuous source, distinct slopes have no positive-mass ties. -/
theorem isUniqueQuadraticOptimalMap_of_maximizes_of_ac_volume
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (ρ : Measure (E d)) [IsProbabilityMeasure ρ]
    {K : Set (E d)} (hK : IsCompact K) (hρ : IsSupported ρ K)
    (hac : ρ ≪ volume) {T : E d → E d} (hT : Measurable T)
    (hmax : ∀ᵐ x ∂ρ, ∃ i, T x = y i ∧ Maximizes y c x i) :
    IsUniqueQuadraticOptimalMap ρ (Measure.map T ρ) T := by
  apply isUniqueQuadraticOptimalMap_of_maximizes_of_compact y c hy ρ hK hρ hT hmax
  filter_upwards [hac.ae_le (ae_affine_tie_implies_slopes_eq volume y c)] with x hx
  intro i j hi hj
  exact hx i j (le_antisymm (hj i) (hi j))

/-- Direct finite-affine uniqueness on a uniform compact source. -/
theorem isUniqueQuadraticOptimalMap_uniform_of_maximizes
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    {K : Set (E d)} (hK : IsCompact K)
    [IsProbabilityMeasure (uniformMeasure K)]
    {T : E d → E d} (hT : Measurable T)
    (hmax : ∀ᵐ x ∂uniformMeasure K, ∃ i, T x = y i ∧ Maximizes y c x i) :
    IsUniqueQuadraticOptimalMap (uniformMeasure K)
      (Measure.map T (uniformMeasure K)) T := by
  apply isUniqueQuadraticOptimalMap_of_maximizes_of_ac_volume y c hy
    (uniformMeasure K) hK (hT := hT) (hmax := hmax)
  · simp [IsSupported, uniformMeasure, Measure.restrict_apply, hK.measurableSet.compl]
  · exact Measure.absolutelyContinuous_restrict.smul_left _

end Problem358.FiniteAffine

end

end OAI
