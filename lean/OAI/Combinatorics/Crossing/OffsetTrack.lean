import OAI.Combinatorics.Crossing.OffsetSegments
import OAI.Combinatorics.Crossing.ParallelDirection
import OAI.Combinatorics.Crossing.FiniteSeparation

namespace OAI

noncomputable section
namespace Zarankiewicz

def trackDirection (v : ℕ → Plane) (i : ℕ) : Plane := v (i+1)-v i

def trackOffset (v : ℕ → Plane) (n i : ℕ) : Plane :=
  if i=0 then normalShift (trackDirection v 0)
  else if i < n then cornerShift (trackDirection v (i-1)) (trackDirection v i)
  else normalShift (trackDirection v (n-1))

def shiftedTrack (v : ℕ → Plane) (n : ℕ) (t : ℝ) (i : ℕ) : Plane :=
  v i+t • trackOffset v n i

theorem trackOffset_incident_levels (v : ℕ → Plane) (n : ℕ)
    (hv : ∀ i, i < n → trackDirection v i ≠ 0)
    (hb : ∀ i, 0 < i → i < n → det2 (trackDirection v (i-1)) (trackDirection v i) ≠ 0)
    (i : ℕ) (hi : i < n) :
    det2 (trackDirection v i) (trackOffset v n i)=1 ∧
      det2 (trackDirection v i) (trackOffset v n (i+1))=1 := by
  constructor
  · by_cases hz : i=0
    · subst i
      simpa [trackOffset] using det2_normalShift (trackDirection v 0) (hv 0 hi)
    · have hip : 0 < i := by omega
      simpa [trackOffset,hz,hi] using
        det2_cornerShift_right (trackDirection v (i-1)) (trackDirection v i) (hb i hip hi)
  · by_cases hnext : i+1 < n
    · simpa [trackOffset,hnext] using
        det2_cornerShift_left (trackDirection v i) (trackDirection v (i+1))
          (by simpa using hb (i+1) (by omega) hnext)
    · have hn : n=i+1 := by omega
      subst n
      simpa [trackOffset] using det2_normalShift (trackDirection v i) (hv i hi)

theorem shiftedTrack_stretch_no_contact (v : ℕ → Plane) (n : ℕ)
    (hv : ∀ i, i < n → trackDirection v i ≠ 0)
    (hb : ∀ i, 0 < i → i < n → det2 (trackDirection v (i-1)) (trackDirection v i) ≠ 0)
    (i : ℕ) (hi : i < n) (t : ℝ) (ht : t ≠ 0) (s r : ℝ) :
    segmentPoint (v i) (v (i+1)) s ≠
      segmentPoint (shiftedTrack v n t i) (shiftedTrack v n t (i+1)) r := by
  have hlevels := trackOffset_incident_levels v n hv hb i hi
  exact offset_segment_no_contact _ _ _ _ t ht hlevels.1 hlevels.2 s r

theorem exists_forward_shiftedTrack_radius (v : ℕ → Plane) (n : ℕ)
    (hv : ∀ i, i < n → trackDirection v i ≠ 0)
    (hb : ∀ i, 0 < i → i < n → det2 (trackDirection v (i-1)) (trackDirection v i) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ i : Fin n,
      ∃ r : ℝ, 0 < r ∧ shiftedTrack v n t (i.val+1)-shiftedTrack v n t i.val = r • trackDirection v i.val := by
  have hh (i : Fin n) := exists_forward_offset_radius (v i.val) (v (i.val+1))
    (trackOffset v n i.val) (trackOffset v n (i.val+1))
    (sub_ne_zero.mp (hv i.val i.isLt))
    (trackOffset_incident_levels v n hv hb i.val i.isLt).1
    (trackOffset_incident_levels v n hv hb i.val i.isLt).2
  choose radius hpos hdir using hh
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun i _ => hpos i)
  exact ⟨δ,hδ,fun t ht i => hdir i t (ht.trans (hbound i (Finset.mem_univ _)))⟩

end Zarankiewicz

end

end OAI
