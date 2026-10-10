import OAI.Combinatorics.Crossing.OffsetTrack
import OAI.Combinatorics.Crossing.OffsetBendSegments
import OAI.Combinatorics.Crossing.ShiftedSegmentStability

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology Classical

theorem exists_shared_track_avoidance_radius (v : ℕ → Plane) (n : ℕ)
    (hv : ∀ i, i < n → trackDirection v i ≠ 0)
    (hb : ∀ i, 0 < i → i < n → det2 (trackDirection v (i-1)) (trackDirection v i) ≠ 0)
    (hfar : ∀ i j : Fin n, i.val+1 < j.val ∨ j.val+1 < i.val →
      ¬ ClosedSegmentsMeet (v i.val) (v (i.val+1)) (v j.val) (v (j.val+1))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ≠ 0 → |t| < δ → ∀ i j : Fin n,
      ¬ ClosedSegmentsMeet (v i.val) (v (i.val+1))
        (shiftedTrack v n t j.val) (shiftedTrack v n t (j.val+1)) := by
  have hevent (ij : Fin n × Fin n) : ∀ᶠ t : ℝ in 𝓝 0,
      (ij.1.val+1 < ij.2.val ∨ ij.2.val+1 < ij.1.val) →
      ¬ ClosedSegmentsMeet (v ij.1.val) (v (ij.1.val+1))
        (shiftedTrack v n t ij.2.val) (shiftedTrack v n t (ij.2.val+1)) := by
    by_cases hh : ij.1.val+1 < ij.2.val ∨ ij.2.val+1 < ij.1.val
    · exact (eventually_shifted_disjoint_segments _ _ _ _ _ _ (hfar ij.1 ij.2 hh)).mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hh h))
  obtain ⟨δ₀,hδ₀,hstable⟩ := finite_eventual_radius _ hevent
  obtain ⟨δ₁,hδ₁,hforward⟩ := exists_forward_shiftedTrack_radius v n hv hb
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro t ht hsmall i j
  have hdir := hforward t (hsmall.trans_le (min_le_right _ _))
  by_cases hij : i=j
  · subst j
    rintro ⟨s,hs,r,hr,he⟩
    exact shiftedTrack_stretch_no_contact v n hv hb i.val i.isLt t ht s r he
  · by_cases hnext : j.val=i.val+1
    · obtain ⟨r,hr,heq⟩ := hdir j
      have hu := (trackOffset_incident_levels v n hv hb i.val i.isLt).2
      have hv' := (trackOffset_incident_levels v n hv hb j.val j.isLt).1
      rw [hnext] at hv'
      have hd : (v (i.val+1+1)+t • trackOffset v n (i.val+1+1))-
          (v (i.val+1)+t • trackOffset v n (i.val+1))=r • (v (i.val+1+1)-v (i.val+1)) := by
        simpa only [shiftedTrack,trackDirection,hnext] using heq
      rintro ⟨s,hs,u,hu',he⟩
      apply incoming_shifted_outgoing_disjoint (v i.val) (v (i.val+1)) (v (i.val+1+1))
        (trackOffset v n (i.val+1)) (trackOffset v n (i.val+1+1)) t r ht hr hu hv' hd s u hs hu'
      simpa only [shiftedTrack,hnext] using he
    · by_cases hprev : i.val=j.val+1
      · obtain ⟨r,hr,heq⟩ := hdir j
        have hu := (trackOffset_incident_levels v n hv hb j.val j.isLt).2
        have hv' := (trackOffset_incident_levels v n hv hb i.val i.isLt).1
        rw [hprev] at hv'
        rintro ⟨s,hs,u,hu',he⟩
        apply outgoing_shifted_incoming_disjoint (v j.val) (v (j.val+1)) (v (j.val+1+1))
          (trackOffset v n j.val) (trackOffset v n (j.val+1)) t r ht hr hu hv' heq s u hs hu'
        simpa only [shiftedTrack,hprev] using he
      · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
        exact hstable t (hsmall.trans_le (min_le_left _ _)) (i,j) (by change i.val+1 < j.val ∨ j.val+1 < i.val; omega)

end Zarankiewicz

end

end OAI
