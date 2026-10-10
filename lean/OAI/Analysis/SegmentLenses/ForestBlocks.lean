import OAI.Analysis.SegmentLenses.DualSums

namespace OAI

/-!
# The finite-height forest as a sum of reflexive blocks
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses


local instance : DecidableEq ForestVertex := Classical.decEq _

section MaximalTests
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]


theorem exists_norming_family (u : Test V) : ∃ F : SegmentFamily V,
    F.seminorm u.coeff = ‖u‖ := by
  classical
  let K := ancestralHull u.coeff.support
  let F₀ : LocalFamily K := ⟨default, by intro S hS; exact False.elim (Finset.notMem_empty _ hS)⟩
  obtain ⟨F, hF, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (LocalFamily K)) (fun F => F.val.seminorm u.coeff)
    (Finset.univ_nonempty_iff.mpr ⟨F₀⟩)
  refine ⟨F.val, le_antisymm (le_segmentSeminorm _ _) ?_⟩
  change segmentSeminorm V u.coeff ≤ _
  rw [segmentSeminorm_apply]
  apply ciSup_le
  intro G
  rw [← G.clip_seminorm (ancestralHull_ancestral _) u.coeff (subset_ancestralHull _)]
  exact hmax ⟨G.clip (ancestralHull_ancestral _), G.clip_subset (ancestralHull_ancestral _)⟩
    (Finset.mem_univ _)

end MaximalTests

section HeightBlocks


def heightTest (h : ℕ) : Test ForestVertex →ₗ[ℝ] Test ForestVertex where
  toFun u := Test.ofFinsupp (u.coeff.filter (fun v => v.val.1 = h))
  map_add' _u _v := Finsupp.filter_add
  map_smul' _c _u := Finsupp.filter_smul

@[simp] theorem heightTest_apply (h : ℕ) (u : Test ForestVertex) (v : ForestVertex) :
    (heightTest h u).coeff v = if v.val.1 = h then u.coeff v else 0 := Finsupp.filter_apply _ _ _

theorem norm_heightTest_le (h : ℕ) (u : Test ForestVertex) : ‖heightTest h u‖ ≤ ‖u‖ := by
  classical
  apply norm_filter_le
  intro a b v ha hb hav hvb
  exact hav.1.symm.trans ha


theorem segment_same_height {S : Finset ForestVertex} (hS : SegmentSystem.isSegment S)
    {v w : ForestVertex} (hv : v ∈ S) (hw : w ∈ S) : v.val.1 = w.val.1 := by
  obtain ⟨a, b, hab, hs⟩ := hS
  exact ((hs v).mp hv).1.1.symm.trans ((hs w).mp hw).1.1


theorem segment_level_injective {S : Finset ForestVertex} (hS : SegmentSystem.isSegment S) :
    Set.InjOn (fun v : ForestVertex => v.val.2.length) S := by
  obtain ⟨a, b, hab, hs⟩ := hS
  intro v hv w hw he
  have hvb := ((hs v).mp hv).2
  have hwb := ((hs w).mp hw).2
  apply Subtype.ext
  refine Prod.ext (hvb.1.trans hwb.1.symm) ?_
  rcases List.prefix_or_prefix_of_prefix hvb.2 hwb.2 with h | h
  · exact h.eq_of_length he
  · exact (h.eq_of_length he.symm).symm

theorem segment_card_bound {S : Finset ForestVertex} (hS : SegmentSystem.isSegment S)
    {h : ℕ} (hc : ∀ v ∈ S, v.val.1 = h) : S.card ≤ h + 1 := by
  classical
  calc
    S.card = (S.image (fun v => v.val.2.length)).card :=
      (Finset.card_image_of_injOn (segment_level_injective hS)).symm
    _ ≤ (Finset.range (h + 1)).card := Finset.card_le_card (by
      intro n hn
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
      apply Finset.mem_range.mpr
      have hh := v.property.2
      rw [hc v hv] at hh
      omega)
    _ = h + 1 := Finset.card_range _


def SegmentFamily.atHeight (F : SegmentFamily ForestVertex) (h : ℕ) :
    SegmentFamily ForestVertex where
  sets := F.sets.filter (fun S => ∀ v ∈ S, v.val.1 = h)
  segment S hS := F.segment S (Finset.mem_filter.mp hS).1
  disjoint := by
    intro S hS T hT hne
    exact F.disjoint (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hT).1 hne

theorem atHeight_seminorm (F : SegmentFamily ForestVertex) (h : ℕ) (u : Test ForestVertex) :
    (F.atHeight h).seminorm u.coeff = F.seminorm (heightTest h u).coeff := by
  have he : (F.atHeight h).seminorm u.coeff ^ 2 = F.seminorm (heightTest h u).coeff ^ 2 := by
    rw [SegmentFamily.seminorm_sq, SegmentFamily.seminorm_sq]
    rw [Finset.sum_coe_sort (F.atHeight h).sets (fun S => (∑ v ∈ S, u.coeff v) ^ 2),
      Finset.sum_coe_sort F.sets (fun S => (∑ v ∈ S, (heightTest h u).coeff v) ^ 2)]
    change (∑ S ∈ F.sets.filter _, _) = ∑ S ∈ F.sets, _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S hS
    split_ifs with hc
    · congr 1
      apply Finset.sum_congr rfl
      intro v hv
      simp only [heightTest_apply, hc v hv, ite_true]
    · have hz : ∀ v ∈ S, v.val.1 ≠ h := by
        intro v hv heq
        apply hc
        intro w hw
        exact (segment_same_height (F.segment S hS) hw hv).trans heq
      simp only [heightTest_apply]
      simp only [Finset.sum_eq_zero (fun v hv => ite_eq_right (hz v hv)), zero_pow (by decide : 2 ≠ 0)]
  nlinarith [apply_nonneg (F.atHeight h).seminorm u.coeff,
    apply_nonneg F.seminorm (heightTest h u).coeff]



theorem height_hilbert_upper (h : ℕ) (u : Test ForestVertex)
    (hu : heightTest h u = u) :
    ‖u‖ ^ 2 ≤ (h + 1 : ℝ) * ∑ v ∈ u.coeff.support, u.coeff v ^ 2 := by
  classical
  obtain ⟨F, hF⟩ := exists_norming_family u
  let G := F.atHeight h
  have hG : G.seminorm u.coeff = ‖u‖ := by rw [atHeight_seminorm, hu, hF]
  rw [← hG, G.seminorm_sq]
  have hlocal : ∀ S : G.sets, (∑ v ∈ S.val, u.coeff v) ^ 2 ≤
      (h + 1 : ℝ) * ∑ v ∈ S.val, u.coeff v ^ 2 := by
    intro S
    have hcs : (∑ v ∈ S.val, u.coeff v) ^ 2 ≤
        (S.val.card : ℝ) * ∑ v ∈ S.val, u.coeff v ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq S.val (fun _ => (1 : ℝ)) (fun v => u.coeff v)
    have hc := segment_card_bound (G.segment _ S.property)
      (Finset.mem_filter.mp S.property).2
    have hcr : (S.val.card : ℝ) ≤ h + 1 := by exact_mod_cast hc
    exact hcs.trans (mul_le_mul_of_nonneg_right hcr (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  calc
    (∑ S : G.sets, (∑ v ∈ S.val, u.coeff v) ^ 2) ≤
        ∑ S : G.sets, (h + 1 : ℝ) * ∑ v ∈ S.val, u.coeff v ^ 2 := Finset.sum_le_sum (fun S _ => hlocal S)
    _ = (h + 1 : ℝ) * ∑ S : G.sets, ∑ v ∈ S.val, u.coeff v ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ (h + 1 : ℝ) * ∑ v ∈ u.coeff.support, u.coeff v ^ 2 := by
      gcongr
      rw [Finset.sum_coe_sort G.sets (fun S => ∑ v ∈ S, u.coeff v ^ 2)]
      have hs : (∑ v ∈ G.sets.biUnion id, u.coeff v ^ 2) =
          ∑ S ∈ G.sets, ∑ v ∈ S, u.coeff v ^ 2 := by
        simpa only [id_eq] using Finset.sum_biUnion (f := fun v => u.coeff v ^ 2) G.disjoint
      rw [← hs]
      have he : (∑ v ∈ G.sets.biUnion id, u.coeff v ^ 2) =
          ∑ v ∈ G.sets.biUnion id ∩ u.coeff.support, u.coeff v ^ 2 := by
        symm
        apply Finset.sum_subset Finset.inter_subset_left
        intro v hv hnv
        have hn : v ∉ u.coeff.support := fun hs => hnv (Finset.mem_inter.mpr ⟨hv, hs⟩)
        simp only [Finsupp.notMem_support_iff.mp hn, zero_pow (by decide : 2 ≠ 0)]
      rw [he]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _ => sq_nonneg _)

end HeightBlocks

section ForestNormDecomposition

def testHeights (u : Test ForestVertex) : Finset ℕ := u.coeff.support.image (fun v => v.val.1)

theorem heightTest_eq_zero {u : Test ForestVertex} {h : ℕ} (hh : h ∉ testHeights u) :
    heightTest h u = 0 := by
  apply Finsupp.ext
  intro v
  change (heightTest h u).coeff v = 0
  rw [heightTest_apply]
  split_ifs with hv
  · apply Finsupp.notMem_support_iff.mp
    intro hs
    exact hh (Finset.mem_image.mpr ⟨v, hs, hv⟩)
  · rfl

theorem heightTest_idem (h : ℕ) (u : Test ForestVertex) :
    heightTest h (heightTest h u) = heightTest h u := by
  apply Finsupp.ext
  intro v
  change (heightTest h (heightTest h u)).coeff v = (heightTest h u).coeff v
  by_cases hv : v.val.1 = h <;> simp [heightTest_apply, hv]

theorem heightTest_ne {h k : ℕ} (hk : h ≠ k) (u : Test ForestVertex) :
    heightTest h (heightTest k u) = 0 := by
  apply Finsupp.ext
  intro v
  change (heightTest h (heightTest k u)).coeff v = 0
  simp only [heightTest_apply]
  split_ifs with hv hv'
  · exact (hk (hv.symm.trans hv')).elim
  · rfl
  · rfl


theorem forest_norm_sq_decomposition (u : Test ForestVertex) :
    ‖u‖ ^ 2 = ∑ h ∈ testHeights u, ‖heightTest h u‖ ^ 2 := by
  classical
  apply le_antisymm
  · obtain ⟨F, hF⟩ := exists_norming_family u
    have he : F.seminorm u.coeff ^ 2 =
        ∑ h ∈ testHeights u, F.seminorm (heightTest h u).coeff ^ 2 := by
      simp_rw [F.seminorm_sq]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S hS
      obtain ⟨a, b, hab, hs⟩ := F.segment S.val S.property
      have hc : ∀ v ∈ S.val, v.val.1 = a.val.1 := fun v hv => ((hs v).mp hv).1.1.symm
      have hv : ∀ h, (∑ v ∈ S.val, (heightTest h u).coeff v) ^ 2 =
          if h = a.val.1 then (∑ v ∈ S.val, u.coeff v) ^ 2 else 0 := by
        intro h
        by_cases hh : h = a.val.1
        · subst h
          simp only [heightTest_apply, Finset.sum_congr rfl (fun v hv => ite_eq_left (hc v hv)), ite_true]
        · have hn : ∀ v ∈ S.val, v.val.1 ≠ h := fun v hv he => hh (he.symm.trans (hc v hv))
          simp only [heightTest_apply, Finset.sum_congr rfl (fun v hv => ite_eq_right (hn v hv)), Finset.sum_const_zero,
            zero_pow (by decide : 2 ≠ 0), ite_eq_right hh]
      simp_rw [hv]
      by_cases ha : a.val.1 ∈ testHeights u
      · simp only [Finset.sum_ite_eq', ite_eq_left ha]
      · have hz : ∑ v ∈ S.val, u.coeff v = 0 := by
          apply Finset.sum_eq_zero
          intro v hv
          apply Finsupp.notMem_support_iff.mp
          intro hvs
          exact ha (Finset.mem_image.mpr ⟨v, hvs, hc v hv⟩)
        simp [hz]
    rw [← hF, he]
    exact Finset.sum_le_sum (fun h _ => sq_le_sq₀ (apply_nonneg _ _) (norm_nonneg _) |>.mpr
      (le_segmentSeminorm _ _))
  · have hex : ∀ h : testHeights u, ∃ F : SegmentFamily ForestVertex,
        F.seminorm (heightTest h.val u).coeff = ‖heightTest h.val u‖ :=
      fun h => exists_norming_family _
    choose F hF using hex
    let G : testHeights u → SegmentFamily ForestVertex := fun h => (F h).atHeight h.val
    have hn : ∀ h, (G h).seminorm u.coeff = ‖heightTest h.val u‖ := by
      intro h
      exact (atHeight_seminorm (F h) h.val u).trans (hF h)
    let pieces : (h : testHeights u) × (G h).sets → Finset ForestVertex := fun j => j.2.val
    have hseg : ∀ j, pieces j = ∅ ∨ SegmentSystem.isSegment (pieces j) := fun j =>
      Or.inr ((G j.1).segment _ j.2.property)
    have hd : Pairwise fun i j => Disjoint (pieces i) (pieces j) := by
      intro i j hij
      by_cases hh : i.1 = j.1
      · rcases i with ⟨i, S⟩
        rcases j with ⟨j, T⟩
        dsimp at hh
        subst j
        exact (G i).disjoint S.property T.property (fun he => hij (by cases Subtype.ext he; rfl))
      · apply Finset.disjoint_left.mpr
        intro v hv hw
        have hvh := (Finset.mem_filter.mp i.2.property).2 v hv
        have hwh := (Finset.mem_filter.mp j.2.property).2 v hw
        exact hh (Subtype.ext (hvh.symm.trans hwh))
    have hb := indexed_test_bound u.coeff pieces hseg hd
    change (∑ j, (∑ v ∈ pieces j, u.coeff v) ^ 2) ≤ ‖u‖ ^ 2 at hb
    rw [Fintype.sum_sigma] at hb
    have he : (∑ h : testHeights u, ∑ S : (G h).sets, (∑ v ∈ S.val, u.coeff v) ^ 2) =
        ∑ h ∈ testHeights u, ‖heightTest h u‖ ^ 2 := by
      rw [← Finset.sum_coe_sort (testHeights u) (fun h => ‖heightTest h u‖ ^ 2)]
      apply Finset.sum_congr rfl
      intro h hh
      rw [← (G h).seminorm_sq, hn]
    exact he ▸ hb

end ForestNormDecomposition

section TestHilbertEmbedding
variable {V : Type*} [DecidableEq V] [segmentSystemV : SegmentSystem V]



def testL2 : Test V →ₗ[ℝ] lp (fun _ : V => ℝ) 2 :=
  (Finsupp.linearCombination ℝ (fun v => lp.single 2 v (1 : ℝ))).comp
    ({ toFun := Test.coeff, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      Test V →ₗ[ℝ] (V →₀ ℝ))

theorem testL2_eq_sum (u : Test V) :
    testL2 u = ∑ v ∈ u.coeff.support, lp.single 2 v (u.coeff v) := by
  have _ := segmentSystemV
  change (∑ v ∈ u.coeff.support, u.coeff v • lp.single 2 v (1 : ℝ)) = _
  simp only [← lp.single_smul, smul_eq_mul, mul_one]

@[simp] theorem testL2_apply (u : Test V) (v : V) : testL2 u v = u.coeff v := by
  classical
  rw [testL2_eq_sum]
  simp only [lp.coeFn_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single v]
  · exact lp.single_apply_self _ _ _
  · intro w hw hwv
    exact lp.single_apply_ne _ _ _ hwv.symm
  · intro hv
    rw [lp.single_apply_self, Finsupp.notMem_support_iff.mp hv]

theorem norm_testL2_sq (u : Test V) : ‖testL2 u‖ ^ 2 = ∑ v ∈ u.coeff.support, u.coeff v ^ 2 := by
  rw [testL2_eq_sum]
  simpa only [Real.norm_eq_abs, sq_abs] using
    l2_norm_sum_single_sq (fun _ : V => ℝ) u.coeff.support (fun v => u.coeff v)

theorem norm_testL2_le (u : Test V) : ‖testL2 u‖ ≤ ‖u‖ := by
  have h := singleton_square_sum_le u.coeff.support u
  rw [← norm_testL2_sq] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

end TestHilbertEmbedding


end SegmentLenses

end

end OAI
