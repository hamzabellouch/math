import OAI.Analysis.CircleDomains.Topology.RoundDiskSlices
import OAI.Analysis.CircleDomains.Selection.FiniteLineGaps

namespace OAI

/-!
# The holes actually crossed by a segment

Only disks meeting the segment are retained. Their horizontal chords lie
strictly between its domain endpoints, are disjoint, and remove exactly
the same points of the segment as the full family of disks.
-/

open Set Function Metric

namespace CircleDomainRigidity

noncomputable def crossingDisks {I : Type*} [Fintype I]
    (c : I → ℂ) (r : I → ℝ) (y a b : ℝ) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => ∃ x ∈ Icc a b, (⟨x, y⟩ : ℂ) ∈ closedBall (c i) (r i))

noncomputable def crossingChords {I : Type*} [Fintype I]
    (c : I → ℂ) (r : I → ℝ) (y a b : ℝ) : Finset (ℝ × ℝ) := by
  classical
  exact (crossingDisks c r y a b).image (fun i => horizontalChord (c i) (r i) y)

@[simp] theorem mem_crossingDisks {I : Type*} [Fintype I]
    {c : I → ℂ} {r : I → ℝ} {y a b : ℝ} {i : I} :
    i ∈ crossingDisks c r y a b ↔
      ∃ x ∈ Icc a b, (⟨x, y⟩ : ℂ) ∈ closedBall (c i) (r i) := by
  classical
  simp [crossingDisks]

theorem crossingDisk_line_hit {I : Type*} [Fintype I]
    {c : I → ℂ} {r : I → ℝ} {y a b : ℝ} {i : I}
    (hi : i ∈ crossingDisks c r y a b) :
    y ∈ Icc ((c i).im - r i) ((c i).im + r i) := by
  obtain ⟨x, _, hx⟩ := mem_crossingDisks.mp hi
  exact (horizontal_line_meets_closedBall (c i)).mp ⟨x, hx⟩

theorem crossingChords_inside {I : Type*} [Fintype I]
    (c : I → ℂ) (r : I → ℝ) {y a b : ℝ} (hr : ∀ i, 0 ≤ r i)
    (ha : ∀ i, (⟨a, y⟩ : ℂ) ∉ closedBall (c i) (r i))
    (hb : ∀ i, (⟨b, y⟩ : ℂ) ∉ closedBall (c i) (r i)) :
    ∀ z ∈ crossingChords c r y a b, a < z.1 ∧ z.1 ≤ z.2 ∧ z.2 < b := by
  classical
  intro z hz
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  have hy := crossingDisk_line_hit hi
  obtain ⟨x, hx, hxi⟩ := mem_crossingDisks.mp hi
  have hends := horizontalChord_inside_segment (hr i) hy (ha i) (hb i)
    ⟨x, hx, (mem_closedBall_iff_mem_horizontalChord _ (hr i) hy).mp hxi⟩
  exact ⟨hends.1, horizontalChord_valid _ _ _, hends.2⟩

theorem crossingChords_disjoint {I : Type*} [Fintype I]
    (c : I → ℂ) (r : I → ℝ) {y a b : ℝ} (hr : ∀ i, 0 ≤ r i)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i))) :
    (↑(crossingChords c r y a b) : Set (ℝ × ℝ)).PairwiseDisjoint (fun z => Icc z.1 z.2) := by
  classical
  intro z hz w hw hzw
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
  have hij : i ≠ j := by intro he; exact hzw (he ▸ rfl)
  exact horizontalChord_disjoint (hr i) (hr j)
    (crossingDisk_line_hit hi) (crossingDisk_line_hit hj) (hdisj hij)

theorem crossingChords_domain {I : Type*} [Fintype I]
    (c : I → ℂ) (r : I → ℝ) {y a b x : ℝ} (hr : ∀ i, 0 ≤ r i) (hx : x ∈ Icc a b) :
    x ∈ (⋃ z ∈ crossingChords c r y a b, Icc z.1 z.2)ᶜ ↔
      (⟨x, y⟩ : ℂ) ∈ (⋃ i, closedBall (c i) (r i))ᶜ := by
  classical
  constructor
  · intro h hball
    obtain ⟨i, hi⟩ := mem_iUnion.mp hball
    have hit : i ∈ crossingDisks c r y a b := mem_crossingDisks.mpr ⟨x, hx, hi⟩
    apply h
    refine mem_iUnion₂.mpr ⟨horizontalChord (c i) (r i) y, Finset.mem_image.mpr ⟨i, hit, rfl⟩, ?_⟩
    exact (mem_closedBall_iff_mem_horizontalChord _ (hr i) (crossingDisk_line_hit hit)).mp hi
  · intro h hchord
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hchord
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    apply h
    exact mem_iUnion.mpr ⟨i,
      (mem_closedBall_iff_mem_horizontalChord _ (hr i) (crossingDisk_line_hit hi)).mpr hxz⟩

end CircleDomainRigidity

end OAI
