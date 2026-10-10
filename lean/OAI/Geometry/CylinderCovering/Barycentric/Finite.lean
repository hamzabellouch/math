import OAI.Geometry.CylinderCovering.Barycentric.EmbeddingArea
import OAI.Geometry.CylinderCovering.Barycentric.Coverage
import OAI.Geometry.CylinderCovering.Barycentric.Correspondence
import OAI.Geometry.CylinderCovering.Barycentric.Cost
import OAI.Geometry.CylinderCovering.Barycentric.Closure

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace RadialCoordinates.BarycentricFinite
open CylinderCovering

lemma firstBase_transport (k : ℝ) (N : ℕ) (i : Fin N) :
    firstBase k N i = IsometricEmbedding.scaledTransportedBase
      (RadialPairedSweep.lowerActualBase (Real.sqrt 2) k (canonicalCap k) N
        (fun j => angular (midpoint N j)) i)
      (RadialPairedSweep.lowerAxis (Real.sqrt 2) k (angular (midpoint N i)))
      canonicalCenter canonicalScale canonicalEmbeddingIsometry := by
  have h := IsometricEmbedding.scaled_projected_image_eq
    (RadialPairedSweep.lowerLocalSweep (Real.sqrt 2) k (canonicalCap k) N i)
    (RadialPairedSweep.lowerAxis (Real.sqrt 2) k (angular (midpoint N i)))
    canonicalCenter canonicalScale canonicalEmbeddingIsometry
  change Similarity.project (canonicalEmbedding
      (RadialPairedSweep.lowerAxis (Real.sqrt 2) k (angular (midpoint N i)))) ''
    (IsometricEmbedding.scaledMap canonicalCenter canonicalScale
      canonicalEmbeddingIsometry '' _) = _ at h
  rw [canonicalEmbedding_lowerAxis, canonical_scaledMap, lowerLocalSweep_image] at h
  exact h

lemma secondBase_transport (k : ℝ) (N : ℕ) (i : Fin N) :
    secondBase k N i = IsometricEmbedding.scaledTransportedBase
      (RadialPairedSweep.upperActualBase (Real.sqrt 2) k (canonicalCap k) N
        (fun j => angular (midpoint N j)) i)
      (RadialPairedSweep.upperAxis (Real.sqrt 2) k (angular (midpoint N i)))
      canonicalCenter canonicalScale canonicalEmbeddingIsometry := by
  have h := IsometricEmbedding.scaled_projected_image_eq
    (RadialPairedSweep.upperLocalSweep (Real.sqrt 2) k (canonicalCap k) N i)
    (RadialPairedSweep.upperAxis (Real.sqrt 2) k (angular (midpoint N i)))
    canonicalCenter canonicalScale canonicalEmbeddingIsometry
  change Similarity.project (canonicalEmbedding
      (RadialPairedSweep.upperAxis (Real.sqrt 2) k (angular (midpoint N i)))) ''
    (IsometricEmbedding.scaledMap canonicalCenter canonicalScale
      canonicalEmbeddingIsometry '' _) = _ at h
  rw [canonicalEmbedding_upperAxis, canonical_scaledMap, upperLocalSweep_image] at h
  exact h

lemma firstAxis_sum (k t : ℝ) : ∑ j, firstAxis k t j = 0 := by
  simp [firstAxis, firstDirection, Fin.sum_univ_four, angular]
  ring

lemma secondAxis_sum (k t : ℝ) : ∑ j, secondAxis k t j = 0 := by
  simp [secondAxis, secondDirection, Fin.sum_univ_four, angular]
  ring

lemma projection_sum {u z : Space} (hu : ∑ j, u j = 0) (hz : ∑ j, z j = 1) :
    ∑ j, projection u z j = 1 := by
  simp only [projection, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hu, hz, mul_zero, sub_zero]

lemma projection_perpendicular {u : Space} (hu : ‖u‖ = 1) (z : Space) :
    inner ℝ u (projection u z) = 0 := by
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  simp [projection, inner_sub_right, inner_smul_right, hu]

lemma mem_projection_cylinder (u : Space) {S : Set Space} {z : Space} (hz : z ∈ S) :
    z ∈ cylinder u (projection u '' S) := by
  refine ⟨projection u z, ⟨z, hz, rfl⟩, inner ℝ u z, ?_⟩
  unfold projection
  module

lemma scaled_base_compact {B : Set RadialCoordinates.Space} (hB : IsCompact B)
    (u : RadialCoordinates.Space) :
    IsCompact (IsometricEmbedding.scaledTransportedBase B u canonicalCenter
      canonicalScale canonicalEmbeddingIsometry) := by
  apply hB.image
  unfold IsometricEmbedding.scaledBaseMap
  fun_prop

lemma firstBase_sum (k : ℝ) (N : ℕ) (i : Fin N) :
    ∀ z ∈ firstBase k N i, ∑ j, z j = 1 := by
  rintro z ⟨x, ⟨t, ht, S, hS, p, hp, rfl⟩, rfl⟩
  exact projection_sum (firstAxis_sum _ _) (firstSweepPoint_sum _ _ _ _)

lemma secondBase_sum (k : ℝ) (N : ℕ) (i : Fin N) :
    ∀ z ∈ secondBase k N i, ∑ j, z j = 1 := by
  rintro z ⟨x, ⟨t, ht, S, hS, p, hp, rfl⟩, rfl⟩
  exact projection_sum (secondAxis_sum _ _) (secondSweepPoint_sum _ _ _ _)

lemma finite_cover {k : ℝ} (hk : 0 < k) (hkbound : k ≤ 1 / 5000)
    {N : ℕ} (hN : 0 < N) :
    ∀ z ∈ barycentricSimplex,
      (∃ i : Fin N, z ∈ cylinder (firstAxis k (midpoint N i)) (firstBase k N i)) ∨
      (∃ i : Fin N, z ∈ cylinder (secondAxis k (midpoint N i)) (secondBase k N i)) := by
  intro z hz
  rcases barycentric_simplex_covered hk hkbound hz with hz | hz
  · rw [firstSweep_eq_parametrizedImage] at hz
    obtain ⟨t, ht, S, hS, p, hp, hz⟩ := hz
    have ht' : t ∈ ⋃ i : Fin N, RadialRiemann.cell 0 1 N i := by
      rw [RadialPartitionCover.equal_cells_cover (by norm_num : (0 : ℝ) ≤ 1) hN]
      exact ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht'
    refine Or.inl ⟨i, mem_projection_cylinder _ ?_⟩
    exact ⟨t, hi, S, hS, p, hp, hz.trans (firstSweepImagePoint_eq _ _ _ _)⟩
  · rw [secondSweep_eq_parametrizedImage] at hz
    obtain ⟨t, ht, S, hS, p, hp, hz⟩ := hz
    have ht' : t ∈ ⋃ i : Fin N, RadialRiemann.cell 0 1 N i := by
      rw [RadialPartitionCover.equal_cells_cover (by norm_num : (0 : ℝ) ≤ 1) hN]
      exact ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht'
    refine Or.inr ⟨i, mem_projection_cylinder _ ?_⟩
    exact ⟨t, hi, S, hS, p, hp, hz.trans (secondSweepImagePoint_eq _ _ _ _)⟩

lemma two_J_eq_scaled_physicalCost (k : ℝ) :
    2 * J k = (1 / 8 : ℝ) *
      (2 * Real.sqrt 2 * RadialPairedSweep.physicalCost (Real.sqrt 2) k (canonicalCap k)) := by
  rw [canonical_physicalCost, J_canonical_cost_identity]
  ring

lemma totalArea_nonneg (k : ℝ) (N : ℕ) : 0 ≤ totalArea k N := by
  unfold totalArea area
  exact add_nonneg (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
    (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)

lemma totalArea_eventually_le (k : ℝ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ N in atTop, totalArea k N ≤ 2 * J k + δ := by
  have h := RadialPairedSweep.paired_actual_sweeps (Real.sqrt 2) k
    (Real.sqrt_pos.mpr (by norm_num)) (canonicalCap k)
    (canonicalCap_continuous k).continuousOn (fun q _ => canonicalCap_nonneg k q)
    (fun N i => angular (midpoint N i)) (fun N i => angular (midpoint N i))
    canonical_midpoint_tagged canonical_midpoint_tagged
  intro δ hδ
  filter_upwards [h.2.1 (8 * δ) (by positivity)] with N hN
  rw [barycentric_totalArea_eq, two_J_eq_scaled_physicalCost]
  linarith

lemma totalArea_limsup_le (k : ℝ) :
    Filter.limsup (totalArea k) atTop ≤ 2 * J k := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  exact _root_.OAI.RadialActualSweep.limsup_le_of_nonneg_of_le_tendsto
    (totalArea_nonneg k) (totalArea_eventually_le k δ hδ) tendsto_const_nhds

lemma base_properties (k : ℝ) {N : ℕ} (hN : 0 < N) (i : Fin N) :
    ‖firstAxis k (midpoint N i)‖ = 1 ∧
    ‖secondAxis k (midpoint N i)‖ = 1 ∧
    IsCompact (firstBase k N i) ∧ IsCompact (secondBase k N i) ∧
    MeasurableSet (firstBase k N i) ∧ MeasurableSet (secondBase k N i) ∧
    Measure.euclideanHausdorffMeasure 2 (firstBase k N i) ≠ ⊤ ∧
    Measure.euclideanHausdorffMeasure 2 (secondBase k N i) ≠ ⊤ ∧
    (∀ z ∈ firstBase k N i,
      inner ℝ (firstAxis k (midpoint N i)) z = 0 ∧ ∑ j, z j = 1) ∧
    (∀ z ∈ secondBase k N i,
      inner ℝ (secondAxis k (midpoint N i)) z = 0 ∧ ∑ j, z j = 1) := by
  have h := RadialPairedSweep.paired_actual_sweeps (Real.sqrt 2) k
    (Real.sqrt_pos.mpr (by norm_num)) (canonicalCap k)
    (canonicalCap_continuous k).continuousOn (fun q _ => canonicalCap_nonneg k q)
    (fun N i => angular (midpoint N i)) (fun N i => angular (midpoint N i))
    canonical_midpoint_tagged canonical_midpoint_tagged
  obtain ⟨hU, hL⟩ := (h.1 N hN).1 i
  have hfirst : ‖firstAxis k (midpoint N i)‖ = 1 := by
    rw [← canonicalEmbedding_lowerAxis, canonicalEmbedding_norm]
    exact hL.1
  have hsecond : ‖secondAxis k (midpoint N i)‖ = 1 := by
    rw [← canonicalEmbedding_upperAxis, canonicalEmbedding_norm]
    exact hU.1
  have hfirstC : IsCompact (firstBase k N i) := by
    rw [firstBase_transport]
    exact scaled_base_compact hL.2.1 _
  have hsecondC : IsCompact (secondBase k N i) := by
    rw [secondBase_transport]
    exact scaled_base_compact hU.2.1 _
  refine ⟨hfirst, hsecond, hfirstC, hsecondC, hfirstC.measurableSet,
    hsecondC.measurableSet, ?_, ?_, ?_, ?_⟩
  · rw [firstBase_transport]
    exact IsometricEmbedding.scaled_transportedBase_finite hL.2.2.2.1 _ _
      canonicalScale_pos.ne' _
  · rw [secondBase_transport]
    exact IsometricEmbedding.scaled_transportedBase_finite hU.2.2.2.1 _ _
      canonicalScale_pos.ne' _
  · intro z hz
    refine ⟨?_, firstBase_sum k N i z hz⟩
    obtain ⟨x, hx, rfl⟩ := hz
    exact projection_perpendicular hfirst x
  · intro z hz
    refine ⟨?_, secondBase_sum k N i z hz⟩
    obtain ⟨x, hx, rfl⟩ := hz
    exact projection_perpendicular hsecond x

theorem finite_barycentric_sweeps : Statement := by
  intro k hk hkbound
  refine ⟨fun N hN => ⟨base_properties k hN, finite_cover hk hkbound hN⟩,
    totalArea_eventually_le k, totalArea_limsup_le k, ?_⟩
  have hgap := J_strict_half_target hk hkbound
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    totalArea_eventually_le k ((Real.sqrt 2 / 4 - 2 * J k) / 2) (by linarith)]
      with N hN hcost
  exact ⟨hN, by linarith⟩

end RadialCoordinates.BarycentricFinite

end

end OAI
