import OAI.Geometry.RuledCovering.Main
import OAI.Geometry.CylinderCovering.Ruled.Similarity

namespace OAI

open Set MeasureTheory Metric
open scoped Topology

noncomputable section
namespace RuledApproximation

theorem compact_coordinates_parallelogram_cover {K : Set Coordinates}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ P : Fin n → Set Coordinates,
      (∀ i, IsParallelogram (P i)) ∧ K ⊆ ⋃ i, P i ∧
      (∑ i, volume.real (P i)) < volume.real K + ε := by
  classical
  have hmodel : LatticeModel (0 : Coordinates →L[ℝ] Coordinates) 1 (1/2) := by
    simpa using nilpotent_lattice_model 0
  obtain ⟨m, hm, S, hS, _, hcover, hcost⟩ := local_finite_certificate
    hK isOpen_univ (subset_univ _) (fun _ => 0) 0
    (show (0:ℝ) ≤ 1 by norm_num) (show (0:ℝ) ≤ 0 by norm_num) hmodel
    (by intros; simp) (continuous_const : Continuous (fun _ : Coordinates => (1:ℝ)))
    (fun _ => zero_le_one) hε
  let : Fintype S := hS.fintype
  let a : ℝ := (1/2) / m
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have ha : 0 < a := div_pos (by norm_num) hmR
  let e := Fintype.equivFin S
  let P : Fin (Fintype.card S) → Set Coordinates :=
    fun i => closedBall ((e.symm i : S) : Coordinates) a
  refine ⟨Fintype.card S, P, fun i => coordinates_closedBall_parallelogram _ ha, ?_, ?_⟩
  · intro p hp
    obtain ⟨b, hb, hdist⟩ := hcover p hp 0 (by norm_num)
    refine mem_iUnion.mpr ⟨e ⟨b, hb⟩, ?_⟩
    change p ∈ closedBall ((e.symm (e ⟨b, hb⟩) : S) : Coordinates) a
    simp only [Equiv.symm_apply_apply]
    rw [mem_closedBall, dist_eq_norm]
    simpa [a] using hdist
  · have harea (b : S) : volume.real (closedBall (b : Coordinates) a) = 1 / (m:ℝ)^2 := by
      rw [coordinates_closedBall_volume _ ha.le]
      dsimp [a]
      ring
    have hsum : (∑ i, volume.real (P i)) = (∑' b : S, (1:ℝ)) / (m:ℝ)^2 := by
      change (∑ i, volume.real (closedBall ((e.symm i : S) : Coordinates) a)) = _
      rw [e.symm.sum_comp (fun b : S => volume.real (closedBall (b : Coordinates) a))]
      simp only [harea, tsum_fintype, Finset.sum_div]
    rw [hsum]
    simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one] using hcost

theorem compact_parallelogram_cover {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 2) {K : Set E} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ P : Fin n → Set E,
      (∀ i, IsParallelogram (P i)) ∧ K ⊆ ⋃ i, P i ∧
      (∑ i, volume.real (P i)) < volume.real K + ε := by
  let e : E ≃ₗᵢ[ℝ] Plane := ((stdOrthonormalBasis ℝ E).reindex (finCongr hdim)).repr
  let M : Coordinates ≃L[ℝ] E :=
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.trans e.symm.toContinuousLinearEquiv
  have hmp : MeasurePreserving M volume volume :=
    e.symm.measurePreserving.comp (PiLp.volume_preserving_toLp (Fin 2))
  have harea (T : Set Coordinates) : volume.real (M '' T) = volume.real T := by
    have h := hmp.setIntegral_image_emb M.toHomeomorph.measurableEmbedding
      (fun _ => (1:ℝ)) T
    simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ,
      smul_eq_mul, mul_one] using h
  let Kc := M.symm '' K
  have hKc : IsCompact Kc := hK.image M.symm.continuous
  have himage : M '' Kc = K := by simp [Kc]
  have hvolume : volume.real Kc = volume.real K := by
    rw [← harea Kc, himage]
  obtain ⟨n, P, hP, hcover, hcost⟩ := compact_coordinates_parallelogram_cover hKc hε
  refine ⟨n, fun i => M '' P i, fun i => (hP i).linear_image M.toLinearMap M.injective,
    ?_, ?_⟩
  · intro x hx
    have hx' : M.symm x ∈ Kc := ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx')
    exact mem_iUnion.mpr ⟨i, M.symm x, hi, M.apply_symm_apply x⟩
  · simp only [harea]
    rwa [hvolume] at hcost

theorem Cylinder.compact_parallelogram_cover (C : Cylinder) (hC : IsCompact C.base)
    {ε : ℝ} (hε : 0 < ε) :
    HasFiniteCover Cylinder.parallelogram C.carrier (C.area + ε) := by
  obtain ⟨n, P, hP, hcover, hcost⟩ := RuledApproximation.compact_parallelogram_cover
    (similarityPlane_finrank C.axis C.unit_axis) hC hε
  let D : Fin n → Cylinder := fun i => ⟨C.axis, C.unit_axis, P i⟩
  refine ⟨n, D, hP, ?_, hcost.le⟩
  rintro x ⟨b, hb, s, rfl⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hb)
  exact mem_iUnion.mpr ⟨i, b, hi, s, rfl⟩

lemma HasFiniteCover.finite_iUnion {ι : Type*} [Fintype ι]
    {shape : Cylinder → Prop} (S : ι → Set Space) (A : ι → ℝ)
    (h : ∀ i, HasFiniteCover shape (S i) (A i)) :
    HasFiniteCover shape (⋃ i, S i) (∑ i, A i) := by
  classical
  have aux (s : Finset ι) : HasFiniteCover shape (⋃ i ∈ s, S i) (∑ i ∈ s, A i) := by
    induction s using Finset.induction_on with
    | empty => simpa using HasFiniteCover.empty shape (show (0:ℝ) ≤ 0 by norm_num)
    | @insert i s hi ih =>
      have heq : (⋃ j ∈ insert i s, S j) = S i ∪ ⋃ j ∈ s, S j := by
        ext x
        simp
      rw [heq, Finset.sum_insert hi]
      exact (h i).union ih
  simpa using aux Finset.univ

theorem compact_family_parallelogram_cover {n : ℕ} (C : Fin n → Cylinder)
    (hC : ∀ i, IsCompact (C i).base) {ε : ℝ} (hε : 0 < ε) :
    HasFiniteCover Cylinder.parallelogram (familySet C) (familyArea C + ε) := by
  have hδ : 0 < ε / (n + 1 : ℝ) := div_pos hε (by positivity)
  have hc := HasFiniteCover.finite_iUnion (fun i => (C i).carrier)
    (fun i => (C i).area + ε / (n + 1 : ℝ))
    (fun i => (C i).compact_parallelogram_cover (hC i) hδ)
  apply hc.mono Subset.rfl
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, familyArea]
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hmul : (n : ℝ) * (ε / (n + 1 : ℝ)) ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ hn]
    nlinarith only [hε]
  linarith only [hmul]

end RuledApproximation

end

end OAI
