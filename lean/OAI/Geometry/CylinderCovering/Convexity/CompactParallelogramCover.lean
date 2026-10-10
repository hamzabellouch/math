import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology

namespace RuledApproximation

theorem compact_coordinate_parallelogram_cover {K : Set Coordinates}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ∃ P : Fin m → Set Coordinates,
      (∀ i, IsParallelogram (P i)) ∧ K ⊆ ⋃ i, P i ∧
      (∑ i, volume.real (P i)) < volume.real K + ε := by
  classical
  obtain ⟨n,hn,S,hS,hSU,hretain,hcost⟩ :=
    (finite_weighted_grid_outer hK isOpen_univ (subset_univ K)
      (continuous_const : Continuous (fun _ : Coordinates => (1 : ℝ)))
      (fun _ => zero_le_one) (1/2) hε).exists
  let : Fintype S := hS.fintype
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let a : ℝ := 1 / (2 * n)
  have ha : 0 < a := by dsimp [a]; positivity
  let Q : S → Set Coordinates := fun b => closedBall (b : Coordinates) a
  have hQ : ∀ b, IsParallelogram (Q b) :=
    fun b => coordinates_closedBall_parallelogram b ha
  have hcov : K ⊆ ⋃ b : S, Q b := by
    intro p hp
    obtain ⟨b,hbg,hbp,hclose⟩ := nilpotent_lattice_model 0 n hn p 0 (by norm_num)
    have hbS : b ∈ S := hretain b hbg ⟨p,hp,by simpa using hbp⟩
    refine mem_iUnion.mpr ⟨⟨b,hbS⟩,?_⟩
    change dist p b ≤ a
    simpa [dist_eq_norm,a] using hclose
  have hQarea (b : S) : volume.real (Q b) = 1 / (n : ℝ)^2 := by
    rw [coordinates_closedBall_volume b ha.le]
    dsimp [a]
    field_simp
  have harea : (∑ b : S, volume.real (Q b)) < volume.real K + ε := by
    simp_rw [hQarea]
    simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, integral_const, measureReal_restrict_apply_univ, smul_eq_mul,
      mul_one, mul_div_assoc, mul_one, div_eq_mul_inv, one_mul] using hcost
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  refine ⟨Fintype.card S, fun i => Q (e.symm i), fun i => hQ _, ?_, ?_⟩
  · intro p hp
    obtain ⟨b,hb⟩ := mem_iUnion.mp (hcov hp)
    exact mem_iUnion.mpr ⟨e b, by simpa using hb⟩
  · rw [e.symm.sum_comp (fun b => volume.real (Q b))]
    exact harea

theorem compact_plane_parallelogram_cover
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hd : Module.finrank ℝ E = 2) {K : Set E} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ∃ P : Fin m → Set E,
      (∀ i, IsParallelogram (P i)) ∧ K ⊆ ⋃ i, P i ∧
      (∑ i, volume.real (P i)) < volume.real K + ε := by
  let b : OrthonormalBasis (Fin 2) ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex (finCongr hd)
  let M : Coordinates ≃L[ℝ] E :=
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.trans b.repr.symm.toContinuousLinearEquiv
  have hMp : MeasurePreserving M volume volume :=
    b.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp (Fin 2))
  have himage (A : Set Coordinates) : volume.real (M '' A) = volume.real A := by
    have h := hMp.measure_preimage_emb M.toHomeomorph.measurableEmbedding (M '' A)
    rw [M.injective.preimage_image] at h
    exact congrArg ENNReal.toReal h.symm
  let Kc : Set Coordinates := M.symm '' K
  have hKc : IsCompact Kc := hK.image M.symm.continuous
  have hMK : M '' Kc = K := by simp [Kc]
  have hKvol : volume.real Kc = volume.real K := by
    rw [← himage Kc,hMK]
  obtain ⟨m,P,hP,hcov,harea⟩ := compact_coordinate_parallelogram_cover hKc hε
  refine ⟨m,fun i => M '' P i,fun i =>
    (hP i).linear_image M.toLinearMap M.injective,?_,?_⟩
  · intro x hx
    have hxc : M.symm x ∈ Kc := mem_image_of_mem _ hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hcov hxc)
    exact mem_iUnion.mpr ⟨i,M.symm x,hi,M.apply_symm_apply x⟩
  · simp_rw [himage]
    rwa [hKvol] at harea

end RuledApproximation

end

end OAI
