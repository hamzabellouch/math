import OAI.Analysis.Brenier.CompactMeasure
import OAI.Analysis.Brenier.Conjugacy
import OAI.Analysis.Brenier.Optimality

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Problem358

/-- A continuous source potential, supporting the map almost everywhere and
having almost everywhere unique differentiable interior slopes, certifies
uniqueness among all transport plans. -/
theorem isUniqueQuadraticOptimalMap_of_ae_differentiable_supporting_potential
    {d : ℕ} {ρ μ : Measure (E d)} [IsFiniteMeasure ρ] [IsFiniteMeasure μ]
    {K Y : Set (E d)} {u : E d → ℝ} {T : E d → E d}
    (hK : IsCompact K) (hne : K.Nonempty) (hY : IsCompact Y)
    (hρ : IsSupported ρ K) (hμ : IsSupported μ Y)
    (hu : ContinuousOn u K) (hT : Measurable T) (hpush : Measure.map T ρ = μ)
    (hdiff : ∀ᵐ x ∂ρ, x ∈ interior K ∧ DifferentiableAt ℝ u x)
    (hs : ∀ᵐ x ∂ρ, ∀ z ∈ K, u x + inner ℝ (z - x) (T x) ≤ u z) :
    IsUniqueQuadraticOptimalMap ρ μ T := by
  let f : E d → ℝ := fun x => ‖x‖ ^ 2 - 2 * u x
  let g : E d → ℝ := fun y => ‖y‖ ^ 2 - 2 * restrictedConjugate K u y
  have hf : Integrable f ρ := hρ.integrable_continuousOn hK
    ((continuous_norm.pow 2).continuousOn.sub (hu.const_mul 2))
  have hg : Integrable g μ := hμ.integrable_continuousOn hY
    (((continuous_norm.pow 2).sub
      ((restrictedConjugate_continuous hK hne hu).const_mul 2)).continuousOn)
  apply isUniqueQuadraticOptimalMap_of_dual hT hpush hf hg
  · intro π hπ
    have hfst : ∀ᵐ p ∂π, p.1 ∈ K := by
      apply ae_of_ae_map measurable_fst.aemeasurable
      rw [hπ.2.1]
      exact ae_iff.mpr hρ
    filter_upwards [hfst] with p hp
    exact restrictedConjugate_quadratic_dual_le hK hu hp p.2
  · have hsource : ∀ᵐ x ∂ρ, x ∈ K := ae_iff.mpr hρ
    filter_upwards [hsource, hs] with x hx hsx
    exact ((restrictedConjugate_quadratic_dual_eq_iff hK hu hx).mpr hsx).symm
  · intro π hπ
    have hfst : ∀ᵐ p ∂π, (p.1 ∈ interior K ∧ DifferentiableAt ℝ u p.1) ∧
        ∀ z ∈ K, u p.1 + inner ℝ (z - p.1) (T p.1) ≤ u z := by
      have he : ∀ᵐ x ∂Measure.map Prod.fst π,
          (x ∈ interior K ∧ DifferentiableAt ℝ u x) ∧
          ∀ z ∈ K, u x + inner ℝ (z - x) (T x) ≤ u z := by
        rw [hπ.2.1]
        exact hdiff.and hs
      exact ae_of_ae_map measurable_fst.aemeasurable he
    filter_upwards [hfst] with p hp
    intro heq
    have hx : p.1 ∈ K := interior_subset hp.1.1
    have hsupport := (restrictedConjugate_quadratic_dual_eq_iff hK hu hx).mp heq
    exact restrictedConjugate_supporting_slope_unique hp.1.1 hp.1.2 hsupport hp.2

/-- For uniform convex sources, Rademacher and the null convex boundary discharge
all differentiability assumptions of the preceding certificate. -/
theorem isUniqueQuadraticOptimalMap_uniform_of_supporting_potential
    {d : ℕ} {K Y : Set (E d)} {μ : Measure (E d)}
    [IsFiniteMeasure (uniformMeasure K)] [IsFiniteMeasure μ]
    {u : E d → ℝ} {T : E d → E d} {L : ℝ≥0}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (hY : IsCompact Y) (hμ : IsSupported μ Y)
    (hu : LipschitzOnWith L u K) (hT : Measurable T)
    (hpush : Measure.map T (uniformMeasure K) = μ)
    (hs : ∀ᵐ x ∂uniformMeasure K, ∀ z ∈ K,
      u x + inner ℝ (z - x) (T x) ≤ u z) :
    IsUniqueQuadraticOptimalMap (uniformMeasure K) μ T := by
  have hρ : IsSupported (uniformMeasure K) K := by
    apply ae_iff.mp
    exact Measure.ae_smul_measure (ae_restrict_mem hK.measurableSet) _
  exact isUniqueQuadraticOptimalMap_of_ae_differentiable_supporting_potential hK hne hY hρ hμ
    hu.continuousOn hT hpush
    (ae_differentiableAt_uniformMeasure hconv hK.measurableSet hu) hs

end Problem358

end

/-! # Optimality and uniqueness from a supporting potential

This packages the limiting-potential step of the arbitrary-target argument.
The potential need only be Lipschitz on the source body and support the
candidate map almost everywhere.  Its restricted conjugate supplies the
dual certificate, and Rademacher regularity makes its equality locus a graph.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace Problem358

/-- A measurable map supported by a Lipschitz potential on a compact convex
source is the unique quadratic optimal plan to its compactly supported law. -/
theorem isUniqueQuadraticOptimalMap_of_supporting_potential
    {d : ℕ} {K Y : Set (E d)} {μ : Measure (E d)} [IsProbabilityMeasure μ]
    {u : E d → ℝ} {T : E d → E d} {L : ℝ≥0}
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hKne : K.Nonempty)
    (hY : IsCompact Y) (hμ : IsSupported μ Y)
    (hu : LipschitzOnWith L u K) (hT : Measurable T)
    (hpush : Measure.map T (uniformMeasure K) = μ)
    (hsupport : ∀ᵐ x ∂uniformMeasure K,
      ∀ z ∈ K, u x + ⟪T x, z - x⟫ ≤ u z) :
    IsUniqueQuadraticOptimalMap (uniformMeasure K) μ T := by
  let : IsProbabilityMeasure (Measure.map T (uniformMeasure K)) :=
    hpush.symm ▸ inferInstance
  let : IsProbabilityMeasure (uniformMeasure K) :=
    Measure.isProbabilityMeasure_of_map hT.aemeasurable
  let v : E d → ℝ := restrictedConjugate K u
  have hv : Continuous v := restrictedConjugate_continuous hK hKne hu.continuousOn
  have hsource : ∀ᵐ x ∂uniformMeasure K, x ∈ K :=
    Measure.ae_smul_measure (ae_restrict_mem hK.measurableSet) _
  have hf : Integrable (fun x : E d => ‖x‖ ^ 2 - 2 * u x) (uniformMeasure K) := by
    apply integrable_of_continuousOn_of_ae_mem_compact hK hsource
    exact (continuous_norm.pow 2).continuousOn.sub (continuousOn_const.mul hu.continuousOn)
  have hg : Integrable (fun y : E d => ‖y‖ ^ 2 - 2 * v y) μ := by
    apply hμ.integrable_continuousOn hY
    exact ((continuous_norm.pow 2).sub (continuous_const.mul hv)).continuousOn
  have hfenchel : ∀ y : E d, ∀ z ∈ K, ⟪z, y⟫ ≤ u z + v y := by
    intro y z hz
    exact restrictedConjugate_fenchel hK hu.continuousOn hz y
  have hstrictSource : ∀ᵐ x ∂uniformMeasure K, ∀ y : E d,
      ⟪x, y⟫ = u x + v y → y = T x := by
    have h := uniform_ae_eq_supporting_map_of_fenchel_eq
      (Y := Set.univ) hKconv hK.measurableSet hu hsupport
      (fun y _ => hfenchel y)
    filter_upwards [h] with x hx
    intro y heq
    exact hx y (Set.mem_univ y) heq
  apply isUniqueQuadraticOptimalMap_of_dual hT hpush hf hg
  · intro π hπ
    have hfst : ∀ᵐ p ∂π, p.1 ∈ K := by
      apply ae_of_ae_map measurable_fst.aemeasurable
      rw [hπ.2.1]
      exact hsource
    filter_upwards [hfst] with p hp
    have h := hfenchel p.2 p.1 hp
    rw [norm_sub_sq_real]
    linarith
  · filter_upwards [hsource, hsupport] with x hx hs
    have heq : ⟪x, T x⟫ = u x + v (T x) := by
      apply (restrictedConjugate_eq_iff_support hK hu.continuousOn hx).mpr
      intro z hz
      simpa only [real_inner_comm (z - x) (T x)] using hs z hz
    rw [norm_sub_sq_real]
    linarith
  · intro π hπ
    have hfst : ∀ᵐ p ∂π, ∀ y : E d,
        ⟪p.1, y⟫ = u p.1 + v y → y = T p.1 := by
      have hm : ∀ᵐ x ∂Measure.map Prod.fst π, ∀ y : E d,
          ⟪x, y⟫ = u x + v y → y = T x := by
        rw [hπ.2.1]
        exact hstrictSource
      exact ae_of_ae_map measurable_fst.aemeasurable hm
    filter_upwards [hfst] with p hp
    intro heq
    apply hp p.2
    rw [norm_sub_sq_real] at heq
    linarith

end Problem358

end

end OAI
