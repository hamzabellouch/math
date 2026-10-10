import OAI.Geometry.DoublingHilbert.Construction

namespace OAI

open MeasureTheory Set Filter
open scoped BigOperators Topology

/-! Intrinsic doubling of the same fixed Hilbert subset. -/

open Set
noncomputable section
namespace DoublingHilbert

/-- A uniform finite set of strips meeting an interval shorter than 128 strip widths. -/
def nearbyStripIndices (c width : ℝ) : Finset ℤ :=
  Finset.Icc (⌊c / width⌋ - 65) (⌊c / width⌋ + 65)

theorem nearbyStripIndices_card (c width : ℝ) : (nearbyStripIndices c width).card = 131 := by
  simp only [nearbyStripIndices, Int.card_Icc]
  omega

theorem mem_nearbyStripIndices {c width t x : ℝ} {q : ℤ}
    (hw : 0 < width) (ht : t / 64 < width) (hx : |x - c| < t)
    (hq : (q : ℝ) * width < x ∧ x < ((q : ℝ) + 1) * width) :
    q ∈ nearbyStripIndices c width := by
  have hxc := abs_lt.mp hx
  have hc₀ := Int.floor_le (c / width)
  have hc₁ := Int.lt_floor_add_one (c / width)
  have hc₀' := (le_div_iff₀ hw).mp hc₀
  have hc₁' := (div_lt_iff₀ hw).mp hc₁
  apply Finset.mem_Icc.mpr
  constructor <;> apply (Int.cast_le (R := ℝ)).mp
  · push_cast
    nlinarith
  · push_cast
    nlinarith

/-- Sixteen cells of width `t/8` cover the coordinate projection of a radius-`t` ball. -/
def coordinateCell (c t x : ℝ) : ℤ := ⌊8 * (x - (c - t)) / t⌋

theorem coordinateCell_mem {c t x : ℝ} (ht : 0 < t) (hx : |x - c| < t) :
    coordinateCell c t x ∈ Finset.Ico (0 : ℤ) 16 := by
  have hxc := abs_lt.mp hx
  have h₀ : 0 ≤ 8 * (x - (c - t)) / t :=
    div_nonneg (by linarith) ht.le
  have h₁ : 8 * (x - (c - t)) / t < 16 := by
    apply (div_lt_iff₀ ht).mpr
    linarith
  rw [Finset.mem_Ico, coordinateCell]
  constructor
  · exact Int.floor_nonneg.mpr h₀
  · exact Int.floor_lt.mpr h₁

theorem abs_sub_lt_of_coordinateCell_eq {c t x y : ℝ} (ht : 0 < t)
    (h : coordinateCell c t x = coordinateCell c t y) : |x - y| < t / 8 := by
  have hx₀ := Int.floor_le (8 * (x - (c - t)) / t)
  have hx₁ := Int.lt_floor_add_one (8 * (x - (c - t)) / t)
  have hy₀ := Int.floor_le (8 * (y - (c - t)) / t)
  have hy₁ := Int.lt_floor_add_one (8 * (y - (c - t)) / t)
  change ⌊8 * (x - (c - t)) / t⌋ = ⌊8 * (y - (c - t)) / t⌋ at h
  rw [← h] at hy₀ hy₁
  have hx₀' := (le_div_iff₀ ht).mp hx₀
  have hx₁' := (div_lt_iff₀ ht).mp hx₁
  have hy₀' := (le_div_iff₀ ht).mp hy₀
  have hy₁' := (div_lt_iff₀ ht).mp hy₁
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end DoublingHilbert


open Set Metric
noncomputable section
namespace DoublingHilbert

/-- A finite coding with fibers of small diameter supplies intrinsic covering centers. -/
theorem cover_of_finite_code {X I : Type*} [PseudoMetricSpace X] [Fintype I]
    (s : Set X) (code : s → I) {r : ℝ}
    (hcode : ∀ x y : s, code x = code y → dist (x : X) (y : X) < r) :
    ∃ centers : Finset X, centers.card ≤ Fintype.card I ∧
      (↑centers : Set X) ⊆ s ∧ ∀ x ∈ s, ∃ y ∈ centers, dist x y < r := by
  classical
  let used : Finset I := Finset.univ.filter (fun i => ∃ x, code x = i)
  let representative : (i : I) → i ∈ used → s := fun i hi =>
    Classical.choose (Finset.mem_filter.mp hi).2
  have hrep : ∀ i hi, code (representative i hi) = i := fun i hi =>
    Classical.choose_spec (Finset.mem_filter.mp hi).2
  let centers : Finset X := used.attach.image (fun i : {i // i ∈ used} => (representative i.val i.prop : X))
  refine ⟨centers, ?_, ?_, ?_⟩
  · exact (Finset.card_image_le).trans (by simpa only [Finset.card_attach] using Finset.card_le_univ used)
  · intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact (representative i i.prop).prop
  · intro x hx
    let xx : s := ⟨x, hx⟩
    have hmem : code xx ∈ used := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨xx, rfl⟩⟩
    refine ⟨representative (code xx) hmem, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨⟨code xx, hmem⟩, Finset.mem_attach _ _, rfl⟩
    · exact hcode xx (representative (code xx) hmem) (hrep (code xx) hmem).symm

/-- Compact metric sets admit a finite upper bound for any fixed positive separation. -/
theorem isCompact_exists_packing_bound {X : Type*} [PseudoMetricSpace X]
    {s : Set X} (hs : IsCompact s) {r : ℝ} (hr : 0 < r) :
    ∃ bound : ℕ, ∀ {n : ℕ} (z : Fin n → X), (∀ i, z i ∈ s) →
      (∀ i j, i ≠ j → r ≤ dist (z i) (z j)) → n ≤ bound := by
  classical
  obtain ⟨t, _, ht, hcover⟩ := hs.finite_cover_balls (show 0 < r / 2 by positivity)
  let := ht.fintype
  refine ⟨Fintype.card t, ?_⟩
  intro n z hz hsep
  have hex : ∀ i, ∃ c : t, dist (z i) c < r / 2 := by
    intro i
    have hi := hcover (hz i)
    simp only [mem_iUnion, mem_ball] at hi
    obtain ⟨c, hc, hdist⟩ := hi
    exact ⟨⟨c, hc⟩, hdist⟩
  choose c hc using hex
  have hinj : Function.Injective c := by
    intro i j hij
    by_contra hne
    have hj := hc j
    rw [← hij] at hj
    have hd := dist_triangle (z i) (c i : X) (z j)
    rw [dist_comm (c i : X) (z j)] at hd
    have hi := hc i
    linarith [hsep i j hne]
  simpa using Fintype.card_le_of_injective c hinj

end DoublingHilbert

namespace DoublingHilbert
open Set
open scoped BigOperators

/-- The finite list of intermediate-level choices near a base point. -/
def nearbyLabels (c : Base) (j : ℕ) : Finset ℕ :=
  insert 0 ((nearbyStripIndices c.2 (scale j)).image
    (fun q => (q % (colors j : ℤ)).toNat + 1) ∪
    (nearbyStripIndices c.1 ((widthFactor j : ℝ) * scale j)).image
      (fun q => (q % (colors j : ℤ)).toNat + 1))

theorem nearbyLabels_card (c : Base) (j : ℕ) : (nearbyLabels c j).card ≤ 300 := by
  have h₁ := Finset.card_image_le (s := nearbyStripIndices c.2 (scale j))
    (f := fun q => (q % (colors j : ℤ)).toNat + 1)
  have h₂ := Finset.card_image_le (s := nearbyStripIndices c.1 ((widthFactor j : ℝ) * scale j))
    (f := fun q => (q % (colors j : ℤ)).toNat + 1)
  rw [nearbyStripIndices_card] at h₁ h₂
  unfold nearbyLabels
  exact (Finset.card_insert_le _ _).trans ((Nat.add_le_add_right
    (Finset.card_union_le _ _) 1).trans (by omega))

theorem admissible_mem_nearbyLabels {c p : Base} {w : Tuple} {j : ℕ} {t : ℝ}
    (hj : t / 64 < scale j) (hp₁ : |p.1 - c.1| < t) (hp₂ : |p.2 - c.2| < t)
    (hw : admissible p w) : w j ∈ nearbyLabels c j := by
  by_cases hzero : w j = 0
  · simp [hzero, nearbyLabels]
  · have ha := (hw j (Finsupp.mem_support_iff.mpr hzero)).2
    have hwid : 1 ≤ (widthFactor j : ℝ) := by exact_mod_cast widthFactor_pos j
    have hwpos : 0 < (widthFactor j : ℝ) * scale j :=
      mul_pos (by linarith) (scale_pos j)
    have hwle : scale j ≤ (widthFactor j : ℝ) * scale j := by nlinarith [scale_pos j]
    have heq {q : ℤ} (hq : q % (colors j : ℤ) = (w j - 1 : ℕ)) :
        (q % (colors j : ℤ)).toNat + 1 = w j := by
      rw [hq, Int.toNat_natCast]
      omega
    rcases ha with ⟨q, hq, hlo, hhi⟩ | ⟨q, hq, hlo, hhi⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨q, mem_nearbyStripIndices (scale_pos j) hj hp₂ ⟨hlo, hhi⟩, heq hq⟩))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨q, mem_nearbyStripIndices hwpos (hj.trans_le hwle) hp₁ ⟨hlo, hhi⟩, heq hq⟩))

/-- Same coarse and intermediate coordinates, and one base cell, force small diameter. -/
theorem point_dist_lt_half {p q : Base} {w w' : Tuple} {t : ℝ} (ht : 0 < t)
    (hx : |p.1 - q.1| < t / 8) (hy : |p.2 - q.2| < t / 8)
    (hlarge : ∀ j, t / 64 < scale j → w j = w' j) :
    dist (point p w) (point q w') < t / 2 := by
  classical
  let s := w.support ∪ w'.support
  let small := s.filter (fun j => scale j ≤ t / 64)
  have hs : ∀ j ∈ small, scale j ≤ t / 64 := fun j hj => (Finset.mem_filter.mp hj).2
  have hsum : (∑ j ∈ s, ‖entryVector w j - entryVector w' j‖ ^ 2) =
      ∑ j ∈ small, ‖entryVector w j - entryVector w' j‖ ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j hj hjs
    have hgt : t / 64 < scale j := by
      simpa only [small, Finset.mem_filter, hj, true_and, not_le] using hjs
    simp [entryVector, hlarge j hgt]
  have hd := point_dist_sq p q w w' s Finset.subset_union_left Finset.subset_union_right
  rw [hsum] at hd
  have htail := fine_tail_le w w' small ht hs
  have hx' : (p.1 - q.1)^2 < (t / 8)^2 := by
    nlinarith [sq_abs (p.1 - q.1), abs_nonneg (p.1 - q.1)]
  have hy' : (p.2 - q.2)^2 < (t / 8)^2 := by
    nlinarith [sq_abs (p.2 - q.2), abs_nonneg (p.2 - q.2)]
  nlinarith [dist_nonneg (x := point p w) (y := point q w'), sq_pos_of_pos ht]

noncomputable def sourceBase (z : constructedSet) : Base := Classical.choose z.prop
noncomputable def sourceTuple (z : constructedSet) : Tuple :=
  Classical.choose (Classical.choose_spec z.prop)

theorem source_admissible (z : constructedSet) : admissible (sourceBase z) (sourceTuple z) :=
  (Classical.choose_spec (Classical.choose_spec z.prop)).1

theorem source_eq_point (z : constructedSet) : (z : RealL2) = point (sourceBase z) (sourceTuple z) :=
  (Classical.choose_spec (Classical.choose_spec z.prop)).2

theorem sourceBase_fst_dist_le (z z' : constructedSet) :
    |(sourceBase z).1 - (sourceBase z').1| ≤ dist z z' := by
  change _ ≤ dist (z : RealL2) (z' : RealL2)
  rw [source_eq_point z, source_eq_point z']
  exact abs_fst_sub_le_dist _ _ _ _

theorem sourceBase_snd_dist_le (z z' : constructedSet) :
    |(sourceBase z).2 - (sourceBase z').2| ≤ dist z z' := by
  change _ ≤ dist (z : RealL2) (z' : RealL2)
  rw [source_eq_point z, source_eq_point z']
  exact abs_snd_sub_le_dist _ _ _ _

theorem sourceTuple_coarse_eq {z z' : constructedSet} {t : ℝ} (hd : dist z z' < t)
    {j : ℕ} (hj : t ≤ scale j) : sourceTuple z j = sourceTuple z' j := by
  apply coarse_coordinate_eq (p := sourceBase z) (q := sourceBase z') (t := t) _ hj
  simpa only [← source_eq_point, Subtype.dist_eq] using hd

/-- Intrinsic centers for any valid intermediate coordinate coding. -/
theorem source_cover_of_label (x : constructedSet) {t : ℝ} (ht : 0 < t)
    (labels : Finset ℕ) (hcard : labels.card ≤ 300)
    (label : Metric.ball x t → {i // i ∈ labels})
    (hlabel : ∀ y z : Metric.ball x t, label y = label z →
      ∀ j, t / 64 < scale j → sourceTuple y.val j = sourceTuple z.val j) :
    ∃ centers : Finset constructedSet, centers.card ≤ 76800 ∧
      ∀ y : constructedSet, dist y x < t → ∃ c ∈ centers, dist y c < t / 2 := by
  classical
  let cells : Finset ℤ := Finset.Ico 0 16
  let key₁ : Metric.ball x t → {i // i ∈ cells} := fun y =>
    ⟨coordinateCell (sourceBase x).1 t (sourceBase y.val).1,
      coordinateCell_mem ht ((sourceBase_fst_dist_le y.val x).trans_lt y.prop)⟩
  let key₂ : Metric.ball x t → {i // i ∈ cells} := fun y =>
    ⟨coordinateCell (sourceBase x).2 t (sourceBase y.val).2,
      coordinateCell_mem ht ((sourceBase_snd_dist_le y.val x).trans_lt y.prop)⟩
  let code := fun y : Metric.ball x t => (key₁ y, key₂ y, label y)
  obtain ⟨centers, hc, _, hcover⟩ := cover_of_finite_code (Metric.ball x t) code
    (r := t / 2) (by
      intro y z heq
      have h₁ := congrArg (fun v => v.1.val) heq
      have h₂ := congrArg (fun v => v.2.1.val) heq
      have hlabel' := congrArg (fun v => v.2.2) heq
      change dist (y.val : RealL2) (z.val : RealL2) < t / 2
      rw [source_eq_point y.val, source_eq_point z.val]
      exact point_dist_lt_half ht (abs_sub_lt_of_coordinateCell_eq ht h₁)
        (abs_sub_lt_of_coordinateCell_eq ht h₂) (hlabel y z hlabel'))
  refine ⟨centers, ?_, hcover⟩
  have hcells : Fintype.card {i // i ∈ cells} = 16 := by
    simp only [Fintype.card_coe, cells, Int.card_Ico]; decide
  simp only [Fintype.card_prod, hcells, Fintype.card_coe] at hc
  omega

/-- The fixed Hilbert subset has an intrinsic open-ball doubling bound of 76800. -/
theorem constructedSet_cover (x : constructedSet) {t : ℝ} (ht : 0 < t) :
    ∃ centers : Finset constructedSet, centers.card ≤ 76800 ∧
      ∀ y : constructedSet, dist y x < t → ∃ c ∈ centers, dist y c < t / 2 := by
  classical
  by_cases hmid : ∃ j, t / 64 < scale j ∧ scale j ≤ t
  · obtain ⟨m, hm⟩ := hmid
    apply source_cover_of_label x ht (nearbyLabels (sourceBase x) m) (nearbyLabels_card _ _)
      (fun y => ⟨sourceTuple y.val m, admissible_mem_nearbyLabels hm.1
        ((sourceBase_fst_dist_le y.val x).trans_lt y.prop)
        ((sourceBase_snd_dist_le y.val x).trans_lt y.prop) (source_admissible y.val)⟩)
    intro y z hyz j hj
    by_cases hjt : scale j ≤ t
    · have heq := intermediate_unique ⟨hj, hjt⟩ hm
      subst j
      exact congrArg Subtype.val hyz
    · exact (sourceTuple_coarse_eq y.prop (le_of_not_ge hjt)).trans
        (sourceTuple_coarse_eq z.prop (le_of_not_ge hjt)).symm
  · apply source_cover_of_label x ht {0} (by simp) (fun _ => ⟨0, by simp⟩)
    intro y z _ j hj
    have hjt : t ≤ scale j := by
      by_contra hn
      exact hmid ⟨j, hj, (not_le.mp hn).le⟩
    exact (sourceTuple_coarse_eq y.prop hjt).trans (sourceTuple_coarse_eq z.prop hjt).symm

end DoublingHilbert

end
end

end OAI
