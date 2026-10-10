import OAI.Analysis.Brenier.AffineOptimality
import OAI.Analysis.Brenier.Cube
import OAI.Analysis.Brenier.SharpMaps

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem358.Sharpness

/-- The concrete map selects a maximizing site in the generic finite-affine interface. -/
lemma slabMap_exists_maximizing_site {d : ℕ} (i j : Fin d) (a b : ℝ)
    (x : E d) :
    ∃ k : Fin 3, slabMap i j a b x = sites i j b k ∧
      FiniteAffine.Maximizes (sites i j b) (intercepts a) x k := by
  obtain ⟨k, hk, ha⟩ := exists_active_site i j a b x
  refine ⟨k, hk, ?_⟩
  intro l
  have hl := site_affine_le_potential i j a b x l
  rw [ha] at hl
  simpa only [real_inner_comm] using hl

/-- The explicit maximum agrees with the generic finite-affine potential. -/
lemma finiteAffine_potential_eq {d : ℕ} (i j : Fin d) (a b : ℝ) :
    FiniteAffine.potential (sites i j b) (intercepts a) = potential i j a b := by
  funext x
  obtain ⟨k, _, hk⟩ := slabMap_exists_maximizing_site i j a b x
  obtain ⟨l, _, hl⟩ := exists_active_site i j a b x
  apply le_antisymm
  · rw [(FiniteAffine.potential_eq_iff_maximizes _ _ _ _).mpr hk]
    simpa only [real_inner_comm] using site_affine_le_potential i j a b x k
  · rw [hl]
    simpa only [real_inner_comm] using
      FiniteAffine.affine_le_potential (sites i j b) (intercepts a) x l

lemma sites_eq_sharpAtoms (d : ℕ) (hd : 2 ≤ d) (b : ℝ) :
    sites (sharpAxis0 d hd) (sharpAxis1 d hd) b = sharpAtoms d hd b := rfl

lemma uniformCube_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (uniformMeasure (cube d)) := by
  constructor
  simp only [uniformMeasure, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul, volume_cube]
  exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)

lemma uniformCube_isSupported (d : ℕ) :
    IsSupported (uniformMeasure (cube d)) (cube d) := by
  rw [IsSupported, uniformMeasure, Measure.smul_apply,
    Measure.restrict_apply (isCompact_cube d).measurableSet.compl]
  simp

lemma uniformCube_absolutelyContinuous (d : ℕ) :
    uniformMeasure (cube d) ≪ (volume : Measure (E d)) := by
  exact (Measure.absolutelyContinuous_of_le
    (Measure.restrict_le_self : volume.restrict (cube d) ≤ volume)).smul_left _

lemma slabMap_compact_range {d : ℕ} (i j : Fin d) (a b : ℝ) :
    IsCompact (Set.range (slabMap i j a b)) := by
  exact ((Set.finite_range (sites i j b)).subset fun x hx => by
    obtain ⟨z, rfl⟩ := hx
    exact slabMap_mem_range_sites i j a b z).isCompact

lemma slabMap_map_supported_sites {d : ℕ} (i j : Fin d) (a b : ℝ)
    (ρ : Measure (E d)) :
    IsSupported (Measure.map (slabMap i j a b) ρ) (Set.range (sites i j b)) := by
  rw [IsSupported, Measure.map_apply (measurable_slabMap i j a b)
    (Set.finite_range (sites i j b)).measurableSet.compl]
  have hempty : slabMap i j a b ⁻¹' (Set.range (sites i j b))ᶜ = ∅ := by
    ext x
    simp [slabMap_mem_range_sites i j a b x]
  rw [hempty, measure_empty]

/-- Every map in the explicit three-plane family is the unique quadratic optimal map
for its law under a compact uniform probability source. -/
theorem slabMap_isUniqueQuadraticOptimalMap_uniform {d : ℕ}
    (K : Set (E d)) [IsProbabilityMeasure (uniformMeasure K)] (hK : IsCompact K)
    (i j : Fin d) (hij : i ≠ j) (a b : ℝ) :
    IsUniqueQuadraticOptimalMap (uniformMeasure K)
      (Measure.map (slabMap i j a b) (uniformMeasure K)) (slabMap i j a b) := by
  apply isUniqueQuadraticOptimalMap_uniform_of_finite_affine K hK
    (sites i j b) (intercepts a) (sites_injective i j hij b)
    (measurable_slabMap i j a b)
  exact Filter.Eventually.of_forall (slabMap_exists_maximizing_site i j a b)

/-- The unique-optimality field of the fixed-cube sharpness construction. -/
theorem slabMap_isUniqueQuadraticOptimalMap_uniformCube {d : ℕ}
    (i j : Fin d) (hij : i ≠ j) (a b : ℝ) :
    IsUniqueQuadraticOptimalMap (uniformMeasure (cube d))
      (Measure.map (slabMap i j a b) (uniformMeasure (cube d))) (slabMap i j a b) := by
  let := uniformCube_isProbabilityMeasure d
  exact slabMap_isUniqueQuadraticOptimalMap_uniform (cube d) (isCompact_cube d) i j hij a b

/-- An identified law immediately gives unique optimality to the named three-atom target. -/
theorem slabMap_isUniqueQuadraticOptimalMap_sharpTarget (d : ℕ) (hd : 2 ≤ d)
    (a b : ℝ)
    (hpush : Measure.map (slabMap (sharpAxis0 d hd) (sharpAxis1 d hd) a b)
      (uniformMeasure (cube d)) = sharpTarget d hd a b) :
    IsUniqueQuadraticOptimalMap (uniformMeasure (cube d)) (sharpTarget d hd a b)
      (slabMap (sharpAxis0 d hd) (sharpAxis1 d hd) a b) := by
  rw [← hpush]
  apply slabMap_isUniqueQuadraticOptimalMap_uniformCube
  simp [sharpAxis0, sharpAxis1]

end Problem358.Sharpness

end

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358

private lemma sharpSource_ae_mem_cube (d : ℕ) :
    ∀ᵐ x ∂uniformMeasure (cube d), x ∈ cube d := by
  unfold uniformMeasure
  exact Measure.ae_smul_measure (ae_restrict_mem (isCompact_cube d).measurableSet) _

private lemma sharpThreshold_nonneg {d : ℕ} (j : Fin d) {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) {x : E d} (hx : x ∈ cube d) :
    0 ≤ a + b * x j := by
  have hxj := (abs_le.mp (hx j)).1
  nlinarith [mul_nonneg hb (show 0 ≤ x j + 1 by linarith)]

/-- The selected negative outer branch has the required probability. -/
lemma uniformMeasure_cube_slab_negative {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (hab : a + b ≤ 1) :
    uniformMeasure (cube d) {x | x ∉ Sharpness.centralCell i j a b ∧ x i < 0} =
      ENNReal.ofReal ((1-a)/2) := by
  rw [← uniformMeasure_cube_leftCell i j hij a b hb hba hab]
  apply measure_congr
  filter_upwards [sharpSource_ae_mem_cube d] with x hx
  have hr := sharpThreshold_nonneg j hb hba hx
  apply propext
  change (¬ |x i| ≤ a + b * x j ∧ x i < 0) ↔ x i < -(a + b * x j)
  constructor
  · rintro ⟨hout, hn⟩
    rw [abs_of_neg hn] at hout
    linarith
  · intro hleft
    have hn : x i < 0 := by linarith
    exact ⟨by rw [abs_of_neg hn]; linarith, hn⟩

/-- The selected positive outer branch has the required probability. -/
lemma uniformMeasure_cube_slab_positive {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (hab : a + b ≤ 1) :
    uniformMeasure (cube d) {x | x ∉ Sharpness.centralCell i j a b ∧ 0 ≤ x i} =
      ENNReal.ofReal ((1-a)/2) := by
  rw [← uniformMeasure_cube_rightCell i j hij a b hb hba hab]
  apply measure_congr
  filter_upwards [sharpSource_ae_mem_cube d] with x hx
  have hr := sharpThreshold_nonneg j hb hba hx
  apply propext
  change (¬ |x i| ≤ a + b * x j ∧ 0 ≤ x i) ↔ a + b * x j < x i
  constructor
  · rintro ⟨hout, hn⟩
    rw [abs_of_nonneg hn] at hout
    exact lt_of_not_ge hout
  · intro hright
    have hn : 0 ≤ x i := by linarith
    exact ⟨by rw [abs_of_nonneg hn]; linarith, hn⟩

/-- The concrete closed slab map has the explicit weighted three-site target law. -/
lemma map_slabMap_uniform_cube {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (hab : a + b ≤ 1) :
    Measure.map (Sharpness.slabMap i j a b) (uniformMeasure (cube d)) =
      ∑ k, sharpWeights a k • Measure.dirac (Sharpness.sites i j b k) := by
  exact Sharpness.map_slabMap_of_cell_masses (uniformMeasure (cube d)) i j a b
    (uniformMeasure_cube_slab_negative i j hij a b hb hba hab)
    (uniformMeasure_cube_slab_positive i j hij a b hb hba hab)
    (uniformMeasure_cube_centralCell i j hij a b hb hba hab)

/-- Target-family form used in the final sharpness example. -/
lemma map_sharpSlab_uniform_cube (d : ℕ) (hd : 2 ≤ d)
    (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (hab : a + b ≤ 1) :
    Measure.map (Sharpness.slabMap (sharpAxis0 d hd) (sharpAxis1 d hd) a b)
      (uniformMeasure (cube d)) = sharpTarget d hd a b := by
  exact map_slabMap_uniform_cube (sharpAxis0 d hd) (sharpAxis1 d hd)
    (sharpAxis_ne d hd) a b hb hba hab

end Problem358

end

end OAI
