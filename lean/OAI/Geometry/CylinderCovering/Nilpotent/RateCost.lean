import OAI.Geometry.CylinderCovering.Nilpotent.SmoothRate
import OAI.Geometry.CylinderCovering.Physical.WeightLipschitz

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace CylinderCovering.NilpotentRate

theorem center_tag_distance {δ R : ℝ} (hδ : 0 ≤ δ) {i : Index} {l b : Plane}
    (hb : b ∈ cell δ i) (hl : Metric.infDist l (cell δ i) ≤ R) :
    ‖l - b‖ ≤ R + Real.sqrt 2 * δ := by
  obtain ⟨p, hp, heq⟩ := (NilpotentGrid.coarseCell_isCompact δ i).exists_infDist_eq_dist
    ⟨b, hb⟩ l
  change Metric.infDist l (cell δ i) = dist l p at heq
  have hlp : ‖l - p‖ ≤ R := by simpa only [heq, dist_eq_norm] using hl
  calc
    ‖l - b‖ = ‖(l - p) + (p - b)‖ := by congr 1; abel
    _ ≤ ‖l - p‖ + ‖p - b‖ := norm_add_le _ _
    _ ≤ R + Real.sqrt 2 * δ := add_le_add hlp (NilpotentGrid.same_cell_distance hδ hp hb)

theorem fine_center_weight_error {δ M K h : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hM : 0 ≤ M) (hK : 0 ≤ K) {G : Plane → Plane} {tag : Index → Plane}
    {i j : Index} {Q : Plane ≃ₗᵢ[ℝ] Plane}
    (htag : tag i ∈ cell δ i) (hAM : ‖fderiv ℝ G (tag i)‖ ≤ M)
    (hret : Metric.infDist (fineCenter δ Q j) (cell δ i) ≤ collarRadius M K δ) :
    |RuledApproximation.physicalWeight h (affineVelocity G tag i (fineCenter δ Q j)) -
      RuledApproximation.physicalWeight h (G (tag i))| ≤
      (max 1 |h| * M * ((1 + M) * (Real.sqrt 2 + K) + Real.sqrt 2)) * δ := by
  have hL : 0 ≤ (1 + M) * (Real.sqrt 2 + K) := by positivity
  have hsq : δ ^ 2 ≤ δ := by nlinarith
  have hdist := center_tag_distance hδ htag hret
  have hdist' : ‖fineCenter δ Q j - tag i‖ ≤
      ((1 + M) * (Real.sqrt 2 + K) + Real.sqrt 2) * δ := by
    have hmul := mul_le_mul_of_nonneg_left hsq hL
    unfold collarRadius at hdist
    nlinarith only [hdist, hmul]
  exact RuledApproximation.affine_physicalWeight_error (fderiv ℝ G (tag i)) hM
    (by positivity) hδ hAM hdist'

theorem fine_weighted_cell_bound {δ M K h : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hM : 0 ≤ M) (hK : 0 ≤ K) {G : Plane → Plane} {tag : Index → Plane}
    {i : Index} {Q : Plane ≃ₗᵢ[ℝ] Plane} (s : Finset Index)
    (htag : tag i ∈ cell δ i) (hAM : ‖fderiv ℝ G (tag i)‖ ≤ M)
    (hret : ∀ j ∈ s, Metric.infDist (fineCenter δ Q j) (cell δ i) ≤ collarRadius M K δ)
    (harea : ∑ j ∈ s, volume.real (tile Q (δ ^ 2) j) ≤
      (δ + 2 * collarRadius M K δ + 2 * Real.sqrt 2 * δ ^ 2) ^ 2) :
    let L := (1 + M) * (Real.sqrt 2 + K)
    let C := 4 * (L + Real.sqrt 2) + 4 * (L + Real.sqrt 2) ^ 2
    let W := max 1 |h| * M * (L + Real.sqrt 2)
    ∑ j ∈ s, volume.real (tile Q (δ ^ 2) j) *
      RuledApproximation.physicalWeight h (affineVelocity G tag i (fineCenter δ Q j)) ≤
      δ ^ 2 * RuledApproximation.physicalWeight h (G (tag i)) + (C + W + C * W) * δ ^ 3 := by
  classical
  dsimp only
  let L := (1 + M) * (Real.sqrt 2 + K)
  let C := 4 * (L + Real.sqrt 2) + 4 * (L + Real.sqrt 2) ^ 2
  let W := max 1 |h| * M * (L + Real.sqrt 2)
  let A := ∑ j ∈ s, volume.real (tile Q (δ ^ 2) j)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ => measureReal_nonneg)
  have hac : A ≤ δ ^ 2 + C * δ ^ 3 := harea.trans
    (_root_.OAI.NilpotentRate.collar_area_bound hδ hδ1 (by unfold collarRadius; positivity) hL le_rfl)
  apply _root_.OAI.NilpotentRate.weighted_cell_bound hδ hδ1 hA
    (by unfold RuledApproximation.physicalWeight; positivity)
    (RuledApproximation.physicalWeight_le_one _ _) hC hW hac
  calc
    _ ≤ ∑ j ∈ s, volume.real (tile Q (δ ^ 2) j) *
        (RuledApproximation.physicalWeight h (G (tag i)) + W * δ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hw : RuledApproximation.physicalWeight h (affineVelocity G tag i (fineCenter δ Q j)) ≤
          RuledApproximation.physicalWeight h (G (tag i)) + W * δ := by
        have he := (abs_le.mp (fine_center_weight_error (h := h) hδ hδ1 hM hK htag hAM (hret j hj))).2
        change _ ≤ W * δ at he
        linarith
      exact mul_le_mul_of_nonneg_left hw measureReal_nonneg
    _ = A * (RuledApproximation.physicalWeight h (G (tag i)) + W * δ) :=
      (Finset.sum_mul s _ _).symm

def secondFiber (s : Finset (Index × Index)) (i : Index) : Finset Index :=
  (s.filter (fun ij => ij.1 = i)).image Prod.snd

theorem sum_pairs_eq_fibers (s : Finset (Index × Index)) (t : Finset Index)
    (hmap : ∀ ij ∈ s, ij.1 ∈ t) (f : Index → Index → ℝ) :
    ∑ ij ∈ s, f ij.1 ij.2 = ∑ i ∈ t, ∑ j ∈ secondFiber s i, f i j := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun ij => f ij.1 ij.2)]
  apply Finset.sum_congr rfl
  intro i hi
  unfold secondFiber
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro ij hij
    rw [(Finset.mem_filter.mp hij).2]
  · intro a ha b hb hab
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) hab

theorem mem_secondFiber {s : Finset (Index × Index)} {i j : Index} :
    j ∈ secondFiber s i ↔ (i, j) ∈ s := by
  classical
  simp only [secondFiber, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨k, l⟩, ⟨hkl, hk⟩, hl⟩
    change k = i at hk
    change l = j at hl
    subst k
    subst l
    exact hkl
  · intro hij
    exact ⟨(i, j), ⟨hij, rfl⟩, rfl⟩

theorem constructionCost_eq_sum {h δ R : ℝ} {D : Set Plane} {G : Plane → Plane}
    {tag : Index → Plane} {Q : Index → Plane ≃ₗᵢ[ℝ] Plane}
    (hfin : (retainedIndices δ R D Q).Finite) :
    constructionCost h δ R D G tag Q =
      ∑ ij ∈ hfin.toFinset, volume.real (tile (Q ij.1) (δ ^ 2) ij.2) *
        RuledApproximation.physicalWeight h (affineVelocity G tag ij.1 (fineCenter δ (Q ij.1) ij.2)) := by
  classical
  let f : Index × Index → ℝ := fun ij => volume.real (tile (Q ij.1) (δ ^ 2) ij.2) *
    RuledApproximation.physicalWeight h (affineVelocity G tag ij.1 (fineCenter δ (Q ij.1) ij.2))
  have he : (∑' ij : (↑hfin.toFinset : Set (Index × Index)), f ij.val) =
      ∑ ij ∈ hfin.toFinset, f ij := by
    rw [tsum_fintype]
    exact Finset.sum_coe_sort hfin.toFinset f
  change (∑' ij : retainedIndices δ R D Q, f ij.val) = ∑ ij ∈ hfin.toFinset, f ij
  let e : retainedIndices δ R D Q ≃ (↑hfin.toFinset : Set (Index × Index)) :=
    { toFun := fun ij => ⟨ij.val, hfin.mem_toFinset.mpr ij.property⟩
      invFun := fun ij => ⟨ij.val, hfin.mem_toFinset.mp ij.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (e.tsum_eq (fun ij => f ij.val)).trans he

def localCostError (M K h : ℝ) : ℝ :=
  let L := (1 + M) * (Real.sqrt 2 + K)
  let C := 4 * (L + Real.sqrt 2) + 4 * (L + Real.sqrt 2) ^ 2
  let W := max 1 |h| * M * (L + Real.sqrt 2)
  C + W + C * W

theorem localCostError_nonneg {M K h : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) :
    0 ≤ localCostError M K h := by
  unfold localCostError
  positivity

theorem constructionCost_le_tagged_sum {δ M K h B : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : 0 ≤ M) (hK : 0 ≤ K) (hB : 0 ≤ B)
    {D : Set Plane} {G : Plane → Plane} {tag : Index → Plane}
    {Q : Index → Plane ≃ₗᵢ[ℝ] Plane}
    (hbound : ∀ x ∈ D, |x 0| ≤ B ∧ |x 1| ≤ B)
    (hfin : (retainedIndices δ (collarRadius M K δ) D Q).Finite)
    (hdata : ∀ i ∈ coarseIndices δ D, tag i ∈ cell δ i ∧ ‖fderiv ℝ G (tag i)‖ ≤ M)
    (harea : ∀ i ∈ coarseIndices δ D, ∀ s : Finset Index,
      (∀ j ∈ s, Metric.infDist (fineCenter δ (Q i) j) (cell δ i) ≤ collarRadius M K δ) →
      ∑ j ∈ s, volume.real (tile (Q i) (δ ^ 2) j) ≤
        (δ + 2 * collarRadius M K δ + 2 * Real.sqrt 2 * δ ^ 2) ^ 2) :
    constructionCost h δ (collarRadius M K δ) D G tag Q ≤
      (∑ i ∈ NilpotentGrid.coarseIndices δ B D,
        δ ^ 2 * RuledApproximation.physicalWeight h (G (tag i))) +
      (2 * B + 4) ^ 2 * localCostError M K h * δ := by
  classical
  let s := hfin.toFinset
  let t := NilpotentGrid.coarseIndices δ B D
  have hi_iff (i : Index) : i ∈ t ↔ i ∈ coarseIndices δ D := by
    rw [NilpotentGrid.mem_coarseIndices_iff hδ hbound]
    exact Set.inter_comm D (cell δ i) ▸ Iff.rfl
  have hmap : ∀ ij ∈ s, ij.1 ∈ t := by
    intro ij hij
    exact (hi_iff ij.1).mpr ((hfin.mem_toFinset.mp hij).1)
  have hret (i : Index) : ∀ j ∈ secondFiber s i,
      Metric.infDist (fineCenter δ (Q i) j) (cell δ i) ≤ collarRadius M K δ := by
    intro j hj
    exact (hfin.mem_toFinset.mp (mem_secondFiber.mp hj)).2
  have hlocal (i : Index) (hi : i ∈ t) :
      ∑ j ∈ secondFiber s i, volume.real (tile (Q i) (δ ^ 2) j) *
        RuledApproximation.physicalWeight h (affineVelocity G tag i (fineCenter δ (Q i) j)) ≤
      δ ^ 2 * RuledApproximation.physicalWeight h (G (tag i)) + localCostError M K h * δ ^ 3 := by
    have hci := (hi_iff i).mp hi
    exact fine_weighted_cell_bound hδ.le hδ1 hM hK (secondFiber s i)
      (hdata i hci).1 (hdata i hci).2 (hret i) (harea i hci _ (hret i))
  rw [constructionCost_eq_sum hfin]
  rw [sum_pairs_eq_fibers s t hmap (fun i j => volume.real (tile (Q i) (δ ^ 2) j) *
    RuledApproximation.physicalWeight h (affineVelocity G tag i (fineCenter δ (Q i) j)))]
  have hs := Finset.sum_le_sum hlocal
  have hc := mul_le_mul_of_nonneg_right (NilpotentGrid.coarse_count_bound D hδ hδ1 hB)
    (mul_nonneg (localCostError_nonneg (h := h) hM hK) hδ.le)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hs
  change _ ≤ _ + (2 * B + 4) ^ 2 * localCostError M K h * δ
  dsimp [t] at hs
  nlinarith only [hs, hc]

end CylinderCovering.NilpotentRate

end

end OAI
