import OAI.MeasureTheory.Falconer.Shells.UnitPairEndgame
import OAI.MeasureTheory.Falconer.Measures.SimilarityMeasures
import OAI.MeasureTheory.Falconer.Estimates.StartingPreparation
import OAI.MeasureTheory.Falconer.Geometry.ProjectionCube
import OAI.MeasureTheory.Falconer.Radial.ClassicalAffineDistance

namespace OAI

/-! # The prepared original pair gives positive measure of original distances -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem prepared_pair_positive_distance
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) (E : Set (Space (m+3))) (hE : IsCompact E)
    (p : PreparedOriginalPair E (1/8)) : 0 < volume (distanceSet E) := by
  classical
  let w : Sphere (m+3) := ⟨p.pair.direction,by
    rw [Metric.mem_sphere,dist_zero_right,p.pair.direction_unit]⟩
  let e := reverseNorthRotation w
  obtain ⟨a,ha,_hcontract,hcube⟩ := compact_projection_into_unitCube E hE
    e.toLinearIsometry.toContinuousLinearMap
  let f := scaledIsometry e a ha
  let F := pairHomeomorph f
  let μ := p.pair.left.map f
  let ν := p.pair.right.map f
  let E' := f '' E
  have hE' : IsCompact E' := hE.image f.continuous
  have hcarr₁ : (μ : Measure (Space (m+3))) (centeredUnitCube (m+3)).carrierᶜ = 0 := by
    change ((p.pair.left : Measure (Space (m+3))).map f) _ = 0
    rw [f.measurableEmbedding.map_apply]
    apply measure_mono_null _ (Measure.measure_compl_support (μ := (p.pair.left : Measure (Space (m+3)))))
    intro x hx hxs
    exact hx (hcube x (p.left_subset hxs))
  have hcarr₂ : (ν : Measure (Space (m+3))) (centeredUnitCube (m+3)).carrierᶜ = 0 := by
    change ((p.pair.right : Measure (Space (m+3))).map f) _ = 0
    rw [f.measurableEmbedding.map_apply]
    apply measure_mono_null _ (Measure.measure_compl_support (μ := (p.pair.right : Measure (Space (m+3)))))
    intro x hx hxs
    exact hx (hcube x (p.right_subset hxs))
  let χ := p.exponent-(m+3:ℕ)/2
  have hχ : 0 < χ := sub_pos.mpr p.exponent_gt
  have hexponent : (m+3:ℕ)/2+χ = p.exponent := by dsimp [χ]; ring
  have hsd : (m+3:ℕ)/2+χ ≤ (m+3:ℕ) := by
    rw [hexponent]
    exact frostman_exponent_le_dimension p.pair.left
      ((by positivity : (0:ℝ) ≤ (m+3:ℕ)/2).trans_lt p.exponent_gt)
      p.pair.constant_pos p.pair.left_frostman
  let C := p.pair.constant/a^p.exponent
  have hC : 0 ≤ C := le_of_lt (div_pos p.pair.constant_pos (Real.rpow_pos_of_pos ha _))
  have hf₁ : FrostmanBallBound (μ : Measure (Space (m+3))) ((m+3:ℕ)/2+χ) C := by
    rw [hexponent]
    exact scaledIsometry_frostman e a ha _ p.pair.left_frostman
  have hf₂ : FrostmanBallBound (ν : Measure (Space (m+3))) ((m+3:ℕ)/2+χ) C := by
    rw [hexponent]
    exact scaledIsometry_frostman e a ha _ p.pair.right_frostman
  have hrelmass : ((μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3)))) (F '' p.pair.relation) = 1 := by
    exact (homeomorph_pair_measure_image f (p.pair.left : Measure (Space (m+3)))
      (p.pair.right : Measure (Space (m+3))) p.pair.relation).trans p.pair.relation_mass
  have hrelmeas : MeasurableSet (F '' p.pair.relation) :=
    F.measurableEmbedding.measurableSet_image.mpr p.pair.relation_measurable
  have hmem := (mem_ae_iff_prob_eq_one hrelmeas).mpr hrelmass
  have hsep : ∀ᵐ z ∂(μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3))),
      a*(p.pair.radius/2) ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ a*(2*p.pair.radius) := by
    filter_upwards [hmem] with z hz
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := hz
    obtain ⟨hl,hu,_⟩ := p.pair.geometry x hxy.1 y hxy.2
    change a*(p.pair.radius/2) ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ a*(2*p.pair.radius)
    rw [scaledIsometry_dist]
    exact ⟨mul_le_mul_of_nonneg_left hl ha.le,mul_le_mul_of_nonneg_left hu ha.le⟩
  have hnear : ∀ᵐ z : Space (m+3) × Space (m+3) ∂(μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3))),
      ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 := by
    filter_upwards [hmem] with z hz
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := hz
    have hh := (p.pair.geometry x hxy.1 y hxy.2).2.2.2.2
    change ‖NormedSpace.normalize (f x-f y)-
      (gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8
    rw [scaledIsometry_normalize_sub,← linearIsometryEquiv_normalize_sub]
    change ‖NormedSpace.normalize (reverseNorthRotation w x-reverseNorthRotation w y)-
      (gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8
    rw [reverseNorthRotation_cap_norm]
    exact hh.le
  have hcarried : ((μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3))))
      ((fun z : Space (m+3) × Space (m+3) => dist z.1 z.2) ⁻¹' (distanceSet E')ᶜ) = 0 := by
    have hnull : ((μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3)))) (F '' p.pair.relation)ᶜ = 0 := hmem
    apply measure_mono_null _ hnull
    rintro z hz ⟨⟨x,y⟩,hxy,rfl⟩
    exact hz ⟨f x,mem_image_of_mem _ (p.left_subset hxy.1),
      f y,mem_image_of_mem _ (p.right_subset hxy.2),rfl⟩
  have hfilters : ∀ ω : ℝ, 0 < ω → ω ≤ 1 →
      ∃ Γ : ℕ → Set (Space (m+3) × Space (m+3)),
        (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧
        0 < ((μ : Measure (Space (m+3))).prod (ν : Measure (Space (m+3)))) (⋂ N, Γ N) ∧
        (∀ N, ∀ z ∈ Γ N, z.1 ≠ z.2) ∧
        (∀ N, HasBorelProductPartition (Γ N) ((2:ℝ)^(2*(m+3:ℕ)*ω*(N:ℝ)))) ∧
        CapAvailable μ ν Γ ((m+3:ℕ)/2) := by
    intro ω hω hω1
    obtain ⟨Γ,hΓ,hm,hpos,hsub,hparts,hcaps⟩ := p.filters ω hω hω1
    refine ⟨fun N => F '' Γ N,fun N => F.measurableEmbedding.measurableSet_image.mpr (hΓ N),
      fun i j hij => Set.image_mono (hm hij),?_,?_,?_,hcaps.scaledIsometry e a ha⟩
    · have he : (⋂ N, F '' Γ N) = F '' (⋂ N, Γ N) := by
        ext z
        obtain ⟨z,rfl⟩ := F.surjective z
        simp only [mem_iInter,F.injective.mem_set_image]
      rw [he]
      exact hpos.trans_le (homeomorph_pair_measure_image f (p.pair.left : Measure (Space (m+3)))
        (p.pair.right : Measure (Space (m+3))) (⋂ N,Γ N)).ge
    · intro N z hz
      obtain ⟨⟨x,y⟩,hxy,rfl⟩ := hz
      change f x ≠ f y
      apply f.injective.ne
      have hh := (p.pair.geometry x (hsub N hxy).1 y (hsub N hxy).2).1
      exact dist_pos.mp ((half_pos p.pair.radius_pos).trans_le hh)
    · intro N
      exact (hparts N).homeomorph f
  apply positive_distance_of_scaledIsometry e a ha E
  exact unit_pair_positive_distance hgnomonic hquadratic m hχ hsd
    (centeredUnitCube _) (centeredUnitCube _) rfl rfl μ ν hcarr₁ hcarr₂ C C hC hC hf₁ hf₂
    (a*(p.pair.radius/2)) (a*(2*p.pair.radius))
    (mul_pos ha (half_pos p.pair.radius_pos))
    (mul_pos ha (mul_pos (by norm_num) p.pair.radius_pos)) hsep hnear
    (distanceSet E') (distanceSet_isCompact hE').measurableSet hcarried hfilters

end Falconer

end OAI
