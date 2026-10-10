import OAI.Geometry.CylinderCovering.Rational.LogarithmicStatementDefinitions
import OAI.Geometry.CylinderCovering.Rational.UncenteredLogarithmic
import OAI.Geometry.CylinderCovering.Rational.DictionaryBridge
import OAI.Geometry.CylinderCovering.Rational.DictionaryExpansion
import OAI.Geometry.CylinderCovering.Rational.Coverage
import OAI.Geometry.CylinderCovering.Rational.Schedules
import OAI.Geometry.CylinderCovering.Rational.Normalization
import OAI.Geometry.CylinderCovering.Ruled.Similarity

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace RationalDictionary

def sweepTurn : Space ≃ₗᵢ[ℝ] Space where
  toFun z := vec3 (z 1) (-z 0) (-z 2)
  invFun z := vec3 (-z 1) (z 0) (-z 2)
  left_inv z := by ext i; fin_cases i <;> simp [vec3]
  right_inv z := by ext i; fin_cases i <;> simp [vec3]
  map_add' z w := by ext i; fin_cases i <;> simp [vec3] <;> ring
  map_smul' r z := by ext i; fin_cases i <;> simp [vec3]
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.real_norm_sq_eq, vec3, Fin.sum_univ_succ]
    ring

def sweepShift : Space := vec3 0 0 2

theorem secondSweep_eq_turn (d0 eta0 k : ℝ) :
    uncenteredSecondSweep d0 eta0 k =
      CylinderCovering.Similarity.map sweepShift 1 sweepTurn ''
        uncenteredFirstSweep d0 eta0 k := by
  apply Set.Subset.antisymm
  · rintro z ⟨p, hp, r, hr, rfl⟩
    refine ⟨vec3 (-r) (lineMap d0 k (-r) p 0) (lineMap d0 k (-r) p 1),
      ⟨p, hp, -r, by simpa only [abs_neg] using hr, rfl⟩, ?_⟩
    ext i
    fin_cases i <;>
      simp [CylinderCovering.Similarity.map, sweepShift, sweepTurn, vec3]
    ring
  · rintro z ⟨w, ⟨p, hp, r, hr, rfl⟩, rfl⟩
    refine ⟨p, hp, -r, by simpa only [abs_neg] using hr, ?_⟩
    ext i
    fin_cases i <;>
      simp [CylinderCovering.Similarity.map, sweepShift, sweepTurn, vec3]
    ring

theorem uncenteredCost_eq_orthonormalCost (d0 eta0 k : ℝ) :
    uncenteredCost d0 eta0 k = orthonormalCost d0 eta0 k := rfl

theorem finite_second_logarithmic {d0 k : ℝ} (hd : 0 < d0)
    (hk : 0 < k) (hkd : k < d0 / (1 + d0)) (eta0 : ℝ)
    {e : ℝ} (he : 0 < e) :
    RuledApproximation.HasFiniteCover RuledApproximation.Cylinder.openBounded
      (uncenteredSecondSweep d0 eta0 k) (orthonormalCost d0 eta0 k + e) := by
  have hfirst := finite_first_logarithmic hd hk hkd eta0 he
  have hsecond := hfirst.openBounded_similarity sweepShift
    (r := (1 : ℝ)) (by norm_num) sweepTurn
  rw [secondSweep_eq_turn]
  simpa only [one_pow, one_mul, uncenteredCost_eq_orthonormalCost] using hsecond

theorem logarithmic_approximations : LogarithmicApproximationStatement := by
  intro d0 hd k hk hkd eta0 e he
  refine ⟨?_, finite_second_logarithmic hd hk hkd eta0 he⟩
  simpa only [uncenteredCost_eq_orthonormalCost] using
    finite_first_logarithmic hd hk hkd eta0 he

def dictionaryReflection : Space ≃ₗᵢ[ℝ] Space where
  toFun z := vec3 (-z 0) (z 1) (-z 2)
  invFun z := vec3 (-z 0) (z 1) (-z 2)
  left_inv z := by ext i; fin_cases i <;> simp [vec3]
  right_inv z := by ext i; fin_cases i <;> simp [vec3]
  map_add' z w := by ext i; fin_cases i <;> simp [vec3] <;> ring
  map_smul' r z := by ext i; fin_cases i <;> simp [vec3]
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.real_norm_sq_eq, vec3, Fin.sum_univ_succ]

theorem phi_eq_similarity : RationalSimilarity.phi =
    CylinderCovering.Similarity.map (vec3 0 0 ell) ell dictionaryReflection := by
  funext z
  ext i
  fin_cases i <;>
    simp [RationalSimilarity.phi, CylinderCovering.Similarity.map,
      dictionaryReflection, vec3, ell, RationalSimilarity.ell]
  ring

theorem phi_injective : Function.Injective RationalSimilarity.phi := by
  rw [phi_eq_similarity]
  exact CylinderCovering.Similarity.map_injective _ ell_ne_zero dictionaryReflection

theorem uncenteredTetrahedron_minimumShadowArea :
    CylinderCovering.minimumShadowArea RationalSimilarity.uncenteredTetrahedron =
      4 * c0 := by
  have himage : CylinderCovering.Similarity.map (vec3 0 0 ell) ell
      dictionaryReflection '' RationalSimilarity.uncenteredTetrahedron =
      SlopeRational.referenceTetrahedron := by
    rw [← phi_eq_similarity, RationalSimilarity.phi_image_tetrahedron,
      centeredTetrahedron_eq_reference]
  have hmin := CylinderCovering.Similarity.minimumArea_map
    RationalSimilarity.uncenteredTetrahedron (vec3 0 0 ell) ell_ne_zero dictionaryReflection
  rw [himage] at hmin
  change CylinderCovering.minimumShadowArea SlopeRational.referenceTetrahedron =
    ell ^ 2 * CylinderCovering.minimumShadowArea RationalSimilarity.uncenteredTetrahedron at hmin
  rw [SlopeRational.referenceTetrahedron_minimumShadowArea, ell_sq] at hmin
  change c0 / 2 = (1 / 8 : ℝ) *
    CylinderCovering.minimumShadowArea RationalSimilarity.uncenteredTetrahedron at hmin
  linarith

theorem centeredTilt_tendsto_right {d0 : ℝ} (hd : 0 < d0) :
    Tendsto (centeredTilt d0) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (centeredTilt d0) 0 := by unfold centeredTilt; fun_prop
    simpa [centeredTilt] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with k hk
    have hkpos : 0 < k := hk
    change 0 < centeredTilt d0 k
    unfold centeredTilt
    positivity

theorem uncentered_coverage_eventually {d0 eta0 : ℝ}
    (hd : 0 < d0) (he : 0 < eta0) :
    ∀ᶠ k : ℝ in 𝓝[>] (0 : ℝ),
      RationalSimilarity.uncenteredTetrahedron ⊆
        uncenteredFirstSweep d0 eta0 k ∪ uncenteredSecondSweep d0 eta0 k := by
  have hmargin : 0 < centeredMargin d0 eta0 := by
    unfold centeredMargin
    positivity
  have hp := SlopeRational.quadratic_padding_conditions hmargin
  have hc := SlopeRational.rationalCoverage_main (centeredRegularization d0)
    (fun eps => centeredMargin d0 eta0 * eps ^ 2)
    (show 0 < centeredRegularization d0 by unfold centeredRegularization; positivity)
    hp.1 hp.2.1 hp.2.2
  filter_upwards [(centeredTilt_tendsto_right hd).eventually hc] with k hk
  rw [← centeredPadding_eq_margin_mul_tilt_sq (by linarith : 1 + d0 ≠ 0)] at hk
  intro z hz
  have hzphi : RationalSimilarity.phi z ∈ SlopeRational.referenceTetrahedron := by
    rw [← centeredTetrahedron_eq_reference, ← RationalSimilarity.phi_image_tetrahedron]
    exact ⟨z, hz, rfl⟩
  rcases hk hzphi with hfirst | hsecond
  · left
    rw [← centeredFirstSweep_eq_lowerSweep, ← phi_image_firstSweep hd eta0 k] at hfirst
    obtain ⟨w, hw, heq⟩ := hfirst
    exact phi_injective heq ▸ hw
  · right
    rw [← centeredSecondSweep_eq_upperSweep, ← phi_image_secondSweep hd eta0 k] at hsecond
    obtain ⟨w, hw, heq⟩ := hsecond
    exact phi_injective heq ▸ hw

theorem strict_logarithmic_of_coverage_cost {d0 eta0 k : ℝ}
    (hd : 0 < d0) (hk : 0 < k) (hkd : k < d0 / (1 + d0))
    (hcov : RationalSimilarity.uncenteredTetrahedron ⊆
      uncenteredFirstSweep d0 eta0 k ∪ uncenteredSecondSweep d0 eta0 k)
    (hcost : orthonormalCost d0 eta0 k < c0) :
    HasStrictLogarithmicCover d0 eta0 k := by
  let e := (c0 - orthonormalCost d0 eta0 k) / 2
  have he : 0 < e := by dsimp [e]; linarith
  obtain ⟨⟨n, C, hC, hCcov, hCa⟩, ⟨m, D, hD, hDcov, hDa⟩⟩ :=
    logarithmic_approximations d0 hd k hk hkd eta0 e he
  have harea : RuledApproximation.familyArea C + RuledApproximation.familyArea D <
      2 * c0 := by
    dsimp [e] at hCa hDa
    linarith
  have hminpos : 0 < CylinderCovering.minimumShadowArea
      RationalSimilarity.uncenteredTetrahedron := by
    rw [uncenteredTetrahedron_minimumShadowArea]
    exact mul_pos (by norm_num) c0_pos
  refine ⟨n, m, C, D, hC, hD, hCcov, hDcov,
    hcov.trans (union_subset_union hCcov hDcov), ?_, ?_⟩
  · rw [uncenteredTetrahedron_minimumShadowArea]
    linarith
  · have hCrel := CylinderCovering.relativeCost_le_familyArea_div_minimum hminpos C
    have hDrel := CylinderCovering.relativeCost_le_familyArea_div_minimum hminpos D
    have hrel := add_le_add hCrel hDrel
    rw [← add_div, uncenteredTetrahedron_minimumShadowArea] at hrel
    apply hrel.trans_lt
    apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) c0_pos)).mpr
    linarith

theorem eventually_strict_logarithmic {d0 eta0 : ℝ}
    (hd : 0 < d0) (he : 0 < eta0)
    (heta : eta0 < coefficientGap d0 / (2 * c0)) :
    ∀ᶠ k : ℝ in 𝓝[>] (0 : ℝ),
      orthonormalCost d0 eta0 k < c0 ∧ HasStrictLogarithmicCover d0 eta0 k := by
  have hsmall : ∀ᶠ k : ℝ in 𝓝[>] (0 : ℝ), k < d0 / (1 + d0) :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (show (0 : ℝ) < d0 / (1 + d0) by positivity))
  filter_upwards [self_mem_nhdsWithin, hsmall,
    uncentered_coverage_eventually hd he, uncenteredCost_eventually_lt hd he heta]
    with k hk hkd hcov hcost
  exact ⟨hcost, strict_logarithmic_of_coverage_cost hd hk hkd hcov hcost⟩

theorem logarithmic_realization : LogarithmicStatement := by
  refine ⟨logarithmic_approximations, uncenteredTetrahedron_minimumShadowArea, ?_, ?_⟩
  · intro d0 hd _ eta0 he heta
    exact eventually_strict_logarithmic hd he heta
  · obtain ⟨d0, hd, eta0, he, heta, _⟩ := exists_uncenteredCost_saving
    exact ⟨d0, hd, eta0, he, heta, eventually_strict_logarithmic hd he heta⟩

end RationalDictionary

end

end OAI
