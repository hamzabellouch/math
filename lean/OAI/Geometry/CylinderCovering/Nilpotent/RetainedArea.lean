import OAI.Geometry.CylinderCovering.Nilpotent.SmoothRateDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory Metric
open scoped Pointwise BigOperators
namespace CylinderCovering.NilpotentRate

private def box (c : Plane) (r : ℝ) : Set Plane :=
  {x | ∀ k, |x k - c k| ≤ r}

private def openBox (c : Plane) (r : ℝ) : Set Plane :=
  {x | ∀ k, |x k - c k| < r}

private lemma box_eq (c : Plane) (r : ℝ) :
    box c r = WithLp.ofLp ⁻¹' Set.pi univ (fun k => Icc (c k-r) (c k+r)) := by
  ext x
  simp only [box, mem_ofPred_eq, mem_preimage, mem_pi, mem_univ, true_implies, mem_Icc]
  constructor <;> intro h k <;> have hk := h k <;> rw [abs_le] at * <;> constructor <;> linarith

private lemma openBox_eq (c : Plane) (r : ℝ) :
    openBox c r = WithLp.ofLp ⁻¹' Set.pi univ (fun k => Ioo (c k-r) (c k+r)) := by
  ext x
  simp only [openBox, mem_ofPred_eq, mem_preimage, mem_pi, mem_univ, true_implies, mem_Ioo]
  constructor <;> intro h k <;> have hk := h k <;> rw [abs_lt] at * <;> constructor <;> linarith

private lemma box_volume (c : Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (box c r) = (2*r)^2 := by
  rw [box_eq, measureReal_def,
    (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage_emb
      (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.measurableEmbedding,
    volume_pi_pi]
  simp only [Real.volume_Icc, Fin.prod_univ_two]
  rw [ENNReal.toReal_mul]
  simp only [show ∀ a : ℝ, a+r-(a-r)=2*r by intro a; ring,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*r)]
  ring

private lemma openBox_volume (c : Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (openBox c r) = (2*r)^2 := by
  rw [openBox_eq, measureReal_def,
    (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage_emb
      (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.measurableEmbedding,
    volume_pi_pi]
  simp only [Real.volume_Ioo, Fin.prod_univ_two]
  rw [ENNReal.toReal_mul]
  simp only [show ∀ a : ℝ, a+r-(a-r)=2*r by intro a; ring,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*r)]
  ring

private lemma box_compact (c : Plane) (r : ℝ) : IsCompact (box c r) := by
  rw [box_eq]
  exact (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.isCompact_preimage.mpr
    (isCompact_univ_pi fun k => isCompact_Icc)

private lemma openBox_open (c : Plane) (r : ℝ) : IsOpen (openBox c r) := by
  simp only [openBox, ofPred_forall]
  exact isOpen_iInter_of_finite fun k => isOpen_lt
    ((continuous_apply k).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous |>.sub continuous_const |>.abs)
    continuous_const

private def indexCoord (i : Index) : Fin 2 → ℤ := ![i.1, i.2]

private lemma integerVector_apply (i : Index) (k : Fin 2) :
    integerVector i k = (indexCoord i k : ℝ) := by
  fin_cases k <;> simp [integerVector, indexCoord, RuledApproximation.vec2]

private lemma tile_eq_rotated_box (Q : Plane ≃ₗᵢ[ℝ] Plane) {τ : ℝ} (hτ : 0 < τ)
    (i : Index) : tile Q τ i = Q '' box (τ • integerVector i) (τ/2) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨τ • (integerVector i+z), ?_, by simp⟩
    intro k
    change |τ * (integerVector i k + z k) - τ * integerVector i k| ≤ τ/2
    have hk := hz k
    rw [show τ * (integerVector i k + z k) - τ * integerVector i k = τ*z k by ring,
      abs_mul, abs_of_pos hτ]
    nlinarith
  · rintro ⟨y, hy, rfl⟩
    refine ⟨τ⁻¹ • y - integerVector i, ?_, ?_⟩
    · intro k
      have hk := hy k
      change |τ⁻¹*y k - integerVector i k| ≤ 1/2
      change |y k - τ*integerVector i k| ≤ τ/2 at hk
      rw [show τ⁻¹*y k-integerVector i k = (y k-τ*integerVector i k)/τ by field_simp,
        abs_div, abs_of_pos hτ]
      exact (div_le_iff₀ hτ).mpr (by linarith)
    · dsimp
      rw [show integerVector i + (τ⁻¹ • y - integerVector i) = τ⁻¹ • y by abel,
        map_smul, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]

private lemma rotated_volume (Q : Plane ≃ₗᵢ[ℝ] Plane) (S : Set Plane) :
    volume.real (Q '' S) = volume.real S := by
  have he : Q '' S = Q.symm ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨Q.symm x, hx, Q.apply_symm_apply x⟩
  rw [he]
  exact congrArg ENNReal.toReal
    (Q.symm.measurePreserving.measure_preimage_emb Q.symm.toHomeomorph.measurableEmbedding S)

lemma tile_area (Q : Plane ≃ₗᵢ[ℝ] Plane) {τ : ℝ} (hτ : 0 < τ) (i : Index) :
    volume.real (tile Q τ i) = τ^2 := by
  rw [tile_eq_rotated_box Q hτ, rotated_volume, box_volume _ (by positivity)]
  congr 1
  ring

lemma tile_compact (Q : Plane ≃ₗᵢ[ℝ] Plane) {τ : ℝ} (hτ : 0 < τ) (i : Index) :
    IsCompact (tile Q τ i) := by
  rw [tile_eq_rotated_box Q hτ]
  exact (box_compact _ _).image Q.continuous

private def openTile (Q : Plane ≃ₗᵢ[ℝ] Plane) (τ : ℝ) (i : Index) : Set Plane :=
  Q '' openBox (τ • integerVector i) (τ/2)

private lemma openTile_subset (Q : Plane ≃ₗᵢ[ℝ] Plane) {τ : ℝ} (hτ : 0 < τ)
    (i : Index) : openTile Q τ i ⊆ tile Q τ i := by
  rw [tile_eq_rotated_box Q hτ]
  exact image_mono fun x hx k => (hx k).le

private lemma openTile_area (Q : Plane ≃ₗᵢ[ℝ] Plane) {τ : ℝ} (hτ : 0 < τ)
    (i : Index) : volume.real (openTile Q τ i) = τ^2 := by
  rw [openTile, rotated_volume, openBox_volume _ (by positivity)]
  congr 1
  ring

private lemma openTile_open (Q : Plane ≃ₗᵢ[ℝ] Plane) (τ : ℝ) (i : Index) :
    IsOpen (openTile Q τ i) :=
  Q.toHomeomorph.isOpenMap _ (openBox_open _ _)

private lemma openTile_disjoint (Q : Plane ≃ₗᵢ[ℝ] Plane) {τ : ℝ} (hτ : 0 < τ) :
    Pairwise (fun i j => Disjoint (openTile Q τ i) (openTile Q τ j)) := by
  intro i j hij
  apply (Set.disjoint_image_iff Q.injective).mpr
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  apply hij
  have he : ∀ k, indexCoord i k = indexCoord j k := by
    intro k
    have hi := abs_lt.mp (hxi k)
    have hj := abs_lt.mp (hxj k)
    simp only [PiLp.smul_apply, smul_eq_mul, integerVector_apply] at hi hj
    have hlt : |((indexCoord i k-indexCoord j k : ℤ) : ℝ)| < 1 := by
      rw [Int.cast_sub, abs_lt]
      constructor <;> nlinarith
    have hint : |indexCoord i k-indexCoord j k| < (1:ℤ) := by exact_mod_cast hlt
    exact sub_eq_zero.mp (Int.abs_lt_one_iff.mp hint)
  exact Prod.ext (he 0) (he 1)

lemma sum_tile_area_le_container (Q : Plane ≃ₗᵢ[ℝ] Plane) {τ : ℝ} (hτ : 0 < τ)
    (s : Finset Index) {E : Set Plane} (hE : volume E ≠ ⊤)
    (hsub : ∀ j ∈ s, tile Q τ j ⊆ E) :
    (∑ j ∈ s, volume.real (tile Q τ j)) ≤ volume.real E := by
  have heq : (∑ j ∈ s, volume.real (tile Q τ j)) =
      volume.real (⋃ j ∈ s, openTile Q τ j) := by
    rw [measureReal_biUnion_finset
      (fun i _ j _ hij => openTile_disjoint Q hτ hij)
      (fun j _ => (openTile_open Q τ j).measurableSet)
      (fun j _ => measure_ne_top_of_subset (openTile_subset Q hτ j)
        (tile_compact Q hτ j).measure_ne_top)]
    exact Finset.sum_congr rfl fun j hj => by rw [tile_area Q hτ, openTile_area Q hτ]
  rw [heq]
  exact measureReal_mono (iUnion₂_subset fun j hj =>
    (openTile_subset Q hτ j).trans (hsub j hj)) hE

lemma unitSquare_norm_le {z : Plane} (hz : z ∈ RuledApproximation.unitSquare) :
    ‖z‖ ≤ Real.sqrt 2 := by
  have h0 := abs_le.mp (hz 0)
  have h1 := abs_le.mp (hz 1)
  have hn := EuclideanSpace.norm_sq_eq z
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hsn := Real.sqrt_nonneg (2:ℝ)
  have hn0 := norm_nonneg z
  nlinarith [sq_nonneg (z 0 - 1/2), sq_nonneg (z 1 - 1/2)]

lemma tile_dist_center_le (Q : Plane ≃ₗᵢ[ℝ] Plane) {τ : ℝ} (hτ : 0 < τ)
    (i : Index) {x : Plane} (hx : x ∈ tile Q τ i) :
    dist x (τ • Q (integerVector i)) ≤ Real.sqrt 2 * τ := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [dist_eq_norm, ← smul_sub, ← map_sub,
    show integerVector i+z-integerVector i=z by abel,
    norm_smul, Q.norm_map, Real.norm_eq_abs, abs_of_pos hτ]
  nlinarith [unitSquare_norm_le hz]

lemma tile_center_mem (Q : Plane ≃ₗᵢ[ℝ] Plane) (τ : ℝ) (i : Index) :
    τ • Q (integerVector i) ∈ tile Q τ i := by
  refine ⟨0, ?_, by simp⟩
  intro k
  norm_num

private def coarseCenter (δ : ℝ) (i : Index) : Plane :=
  RuledApproximation.vec2 (δ*((i.1:ℝ)+1/2)) (δ*((i.2:ℝ)+1/2))

private lemma cell_eq_box {δ : ℝ} (_hδ : 0 < δ) (i : Index) :
    cell δ i = box (coarseCenter δ i) (δ/2) := by
  ext x
  change (δ*(i.1:ℝ) ≤ x 0 ∧ x 0 ≤ δ*((i.1:ℝ)+1) ∧
    δ*(i.2:ℝ) ≤ x 1 ∧ x 1 ≤ δ*((i.2:ℝ)+1)) ↔ _
  constructor
  · intro hx k
    fin_cases k
    · change |x 0-δ*((i.1:ℝ)+1/2)| ≤ δ/2
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2.1]
    · change |x 1-δ*((i.2:ℝ)+1/2)| ≤ δ/2
      rw [abs_le]
      constructor <;> linarith [hx.2.2.1, hx.2.2.2]
  · intro hx
    have h0 := hx 0
    have h1 := hx 1
    change |x 0-δ*((i.1:ℝ)+1/2)| ≤ δ/2 at h0
    change |x 1-δ*((i.2:ℝ)+1/2)| ≤ δ/2 at h1
    rw [abs_le] at h0 h1
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private lemma retained_tile_subset_box {δ τ R : ℝ} (hδ : 0 < δ) (hτ : 0 < τ)
    (Q : Plane ≃ₗᵢ[ℝ] Plane) (i j : Index)
    (hj : infDist (τ • Q (integerVector j)) (cell δ i) ≤ R) :
    tile Q τ j ⊆ box (coarseCenter δ i) (δ/2+R+Real.sqrt 2*τ) := by
  have hc : IsCompact (cell δ i) := by rw [cell_eq_box hδ i]; exact box_compact _ _
  have hne : (cell δ i).Nonempty := by
    rw [cell_eq_box hδ i]
    refine ⟨coarseCenter δ i, ?_⟩
    intro k
    simp only [sub_self, abs_zero]
    positivity
  obtain ⟨y, hy, hdist⟩ := hc.exists_infDist_eq_dist hne (τ • Q (integerVector j))
  have hdy : dist (τ • Q (integerVector j)) y ≤ R := hdist.symm ▸ hj
  rw [cell_eq_box hδ i] at hy
  intro x hx k
  have hdx := tile_dist_center_le Q hτ j hx
  have hxy : dist x y ≤ Real.sqrt 2*τ+R :=
    (dist_triangle x (τ • Q (integerVector j)) y).trans (add_le_add hdx hdy)
  have hcoord : |x k-y k| ≤ dist x y := by
    simpa only [Real.norm_eq_abs, PiLp.sub_apply, dist_eq_norm] using
      PiLp.norm_apply_le (x-y) k
  have habs := abs_add_le (x k-y k) (y k-(coarseCenter δ i) k)
  have hyk := hy k
  change |x k-(coarseCenter δ i) k| ≤ δ/2+R+Real.sqrt 2*τ
  rw [sub_add_sub_cancel] at habs
  linarith

lemma retained_tile_area_bound {δ τ R : ℝ} (hδ : 0 < δ) (hτ : 0 < τ) (hR : 0 ≤ R)
    (Q : Plane ≃ₗᵢ[ℝ] Plane) (i : Index) (s : Finset Index)
    (hs : ∀ j ∈ s, infDist (τ • Q (integerVector j)) (cell δ i) ≤ R) :
    (∑ j ∈ s, volume.real (tile Q τ j)) ≤ (δ+2*R+2*Real.sqrt 2*τ)^2 := by
  have h := sum_tile_area_le_container Q hτ s
    (box_compact (coarseCenter δ i) (δ/2+R+Real.sqrt 2*τ)).measure_ne_top
    (fun j hj => retained_tile_subset_box hδ hτ Q i j (hs j hj))
  rw [box_volume _ (by positivity)] at h
  convert h using 1
  ring

lemma retained_fine_area_bound {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R)
    (Q : Plane ≃ₗᵢ[ℝ] Plane) (i : Index) (s : Finset Index)
    (hs : ∀ j ∈ s, infDist (fineCenter δ Q j) (cell δ i) ≤ R) :
    (∑ j ∈ s, volume.real (tile Q (δ^2) j)) ≤
      (δ+2*R+2*Real.sqrt 2*δ^2)^2 :=
  retained_tile_area_bound hδ (sq_pos_of_pos hδ) hR Q i s hs

private lemma openTile_ae_eq_tile (Q : Plane ≃ₗᵢ[ℝ] Plane) {τ : ℝ}
    (hτ : 0 < τ) (i : Index) : openTile Q τ i =ᵐ[volume] tile Q τ i := by
  have ht := (tile_compact Q hτ i).measure_ne_top (μ := volume)
  have ho := measure_ne_top_of_subset (openTile_subset Q hτ i) ht
  apply ae_eq_of_subset_of_measure_ge (openTile_subset Q hτ i) _
    (openTile_open Q τ i).measurableSet.nullMeasurableSet ht
  apply (ENNReal.toReal_le_toReal ht ho).mp
  change volume.real (tile Q τ i) ≤ volume.real (openTile Q τ i)
  rw [tile_area Q hτ, openTile_area Q hτ]

lemma tile_aedisjoint (Q : Plane ≃ₗᵢ[ℝ] Plane) {τ : ℝ} (hτ : 0 < τ) :
    Pairwise (fun i j => AEDisjoint volume (tile Q τ i) (tile Q τ j)) := by
  intro i j hij
  exact (openTile_disjoint Q hτ hij).aedisjoint.congr
    (openTile_ae_eq_tile Q hτ i).symm (openTile_ae_eq_tile Q hτ j).symm

lemma finite_tile_union_area (Q : Plane ≃ₗᵢ[ℝ] Plane) {τ : ℝ} (hτ : 0 < τ)
    (s : Finset Index) :
    volume.real (⋃ j ∈ s, tile Q τ j) = ∑ j ∈ s, volume.real (tile Q τ j) := by
  exact measureReal_biUnion_finset₀
    (fun i _ j _ hij => tile_aedisjoint Q hτ hij)
    (fun j _ => (tile_compact Q hτ j).measurableSet.nullMeasurableSet)
    (fun j _ => (tile_compact Q hτ j).measure_ne_top)

end CylinderCovering.NilpotentRate

end

end OAI
