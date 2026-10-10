import OAI.Analysis.CircleDomains.Selection.SortedChordGapAvoidance
import OAI.Analysis.CircleDomains.Selection.FiniteHoleSliceAssembly
import OAI.Analysis.CircleDomains.Rigidity.AxialSwapDisks

namespace OAI

/-! The numerical gap estimate applied to the actual finite disk family.
The scalar premise is the interval estimate from the common-point
trace theorem. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity

 theorem axial_disk_toll_eq_hit (i : Fin 2) (c : ℂ) (r s y : ℝ) :
    (Icc (transverseCoordinate i c-r) (transverseCoordinate i c+r)).indicator
      (fun _ => 2*s) y =
      if {x | complexCoordinateLine i y x ∈ closedBall c r}.Nonempty then 2*s else 0 := by
  have he : {x | complexCoordinateLine i y x ∈ closedBall c r}.Nonempty ↔
      y ∈ Icc (transverseCoordinate i c-r) (transverseCoordinate i c+r) :=
    complexCoordinateLine_meets_closedBall i y c r
  by_cases h : y ∈ Icc (transverseCoordinate i c-r) (transverseCoordinate i c+r)
  · rw [indicator_of_mem h,ite_eq_left (he.mpr h)]
  · rw [indicator_of_notMem h,ite_eq_right (fun h' => h (he.mp h'))]

 theorem finite_disk_slice_payment {κ : Type*} [Countable κ]
    (i : Fin 2) (c : κ → ℂ) (r s : κ → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hs : ∀ j, 0 ≤ s j)
    (F : Finset κ) {η : ℝ} (hη : 0 < η)
    (hd : Pairwise (Disjoint on fun j : F => closedBall (c j) (r j+η)))
    (hone : ∀ k ∉ F, ∀ j ∈ F, ∀ l ∈ F,
      (closedBall (c k) (r k) ∩ closedBall (c j) (r j+η)).Nonempty →
      (closedBall (c k) (r k) ∩ closedBall (c l) (r l+η)).Nonempty → j = l)
    {y a b : ℝ} (hab : a < b)
    (ha : ∀ j ∈ F, complexCoordinateLine i y a ∉ closedBall (c j) (r j+η))
    (hb : ∀ j ∈ F, complexCoordinateLine i y b ∉ closedBall (c j) (r j+η))
    (htoll : Summable (fun j : {j : κ // j ∉ F} =>
      (Icc (transverseCoordinate i (c j)-r j) (transverseCoordinate i (c j)+r j)).indicator
        (fun _ => 2*s j) y))
    (v ρ : ℝ → ℝ) {V : Set ℝ} (hV : MeasurableSet V)
    (hi : IntegrableOn ρ (Icc a b ∩ V) volume) (hρ : ∀ x ∈ Icc a b ∩ V, 0 ≤ ρ x)
    (hpay : ∀ u w : ℝ, u ≤ w → Icc u w ⊆ Icc a b →
      (∀ x ∈ Icc u w, ∀ j ∈ F, complexCoordinateLine i y x ∉ closedBall (c j) (r j)) →
      |v w-v u| ≤ (∫ x in Icc u w ∩ V, ρ x) +
        ∑' j : {j : κ // j ∉ F},
          if ∃ x ∈ Icc u w, complexCoordinateLine i y x ∈ closedBall (c j) (r j)
          then 2*s j else 0) :
    v b-v a-
      (∑ j ∈ crossingDisks (fun j : F => axialSwap i (c j)) (fun j => r j+η) y a b,
        (v (axialChord i (c j) (r j+η) y).2-v (axialChord i (c j) (r j+η) y).1)) ≤
      (∫ x in Icc a b ∩ V, ρ x)+
        2*axialDiskToll i (fun j : {j : κ // j ∉ F} => c j) (fun j => r j) (fun j => s j) y := by
  let c' : F → ℂ := fun j => axialSwap i (c j)
  let r' : F → ℝ := fun j => r j+η
  have hr' (j : F) : 0 ≤ r' j := add_nonneg (hr j) hη.le
  obtain ⟨S⟩ := exists_sorted_crossing_chords c' r' hr'
    (axialSwap_pairwise_disjoint i _ _ hd)
    (fun j hj => ha j j.property ((horizontal_mem_swapped_disk i a y (c j) (r j+η)).mp hj))
    (fun j hj => hb j j.property ((horizontal_mem_swapped_disk i b y (c j) (r j+η)).mp hj))
  let J : {j : κ // j ∉ F} → Set ℝ := fun j => {x | complexCoordinateLine i y x ∈ closedBall (c j) (r j)}
  have ht : Summable (fun j => if (J j).Nonempty then 2*s j else 0) := by
    simpa only [axial_disk_toll_eq_hit] using htoll
  have hgap (k : Fin (S.count+1)) :
      Icc (gapsAfterHoles a b S.hole k).1 (gapsAfterHoles a b S.hole k).2 ⊆ Icc a b :=
    closed_gaps_inside S.hole (fun j => ⟨(S.inside j).1.le,(S.inside j).2.1,(S.inside j).2.2.le⟩) k
  have hp (k : Fin (S.count+1)) := hpay _ _
    (gapsAfterHoles_strict hab S.hole S.inside S.separated k).le (hgap k) (by
      intro x hx j hj hxj
      have havoid := S.closed_gap_avoids_original hr' (fun j : F => r j)
        (fun j => by dsimp [r']; linarith) k hx ⟨j,hj⟩
      exact havoid ((horizontal_mem_swapped_disk i x y (c j) (r j)).mpr hxj))
  have hbound := finite_hole_slice_payment a b S.hole (fun j => (S.inside j).2.1)
    S.monotone_first J (fun j => 2*s j) (fun j => mul_nonneg (by norm_num) (hs j)) ht
    (fun j => axial_ball_preimage_ordConnected i y (c j) (hr j)) (by
      intro k j l hj hl
      apply S.owner_injective
      apply Subtype.ext
      apply hone k k.property (S.owner j) (S.owner j).property (S.owner l) (S.owner l).property
      · obtain ⟨x,hx,hxj⟩ := hj
        refine ⟨complexCoordinateLine i y x,hx,?_⟩
        apply (horizontal_mem_swapped_disk i x y _ _).mp
        apply (mem_closedBall_iff_mem_horizontalChord _ (hr' _) (crossingDisk_line_hit (S.owner_mem j))).mpr
        simpa only [S.hole_eq] using hxj
      · obtain ⟨x,hx,hxl⟩ := hl
        refine ⟨complexCoordinateLine i y x,hx,?_⟩
        apply (horizontal_mem_swapped_disk i x y _ _).mp
        apply (mem_closedBall_iff_mem_horizontalChord _ (hr' _) (crossingDisk_line_hit (S.owner_mem l))).mpr
        simpa only [S.hole_eq] using hxl)
    v ρ (measurableSet_Icc.inter hV) hV hi hρ
    (fun k x hx => ⟨hgap k hx.1,hx.2⟩) (by
      intro k
      exact (le_abs_self _).trans (by simpa only [J,Set.nonempty_def,mem_inter_iff,mem_ofPred_eq,and_comm] using hp k))
  rw [S.sum_hole_increments] at hbound
  simpa only [c',r',axialChord,axialDiskToll,axial_disk_toll_eq_hit] using hbound

end CircleDomainRigidity

end

end OAI
