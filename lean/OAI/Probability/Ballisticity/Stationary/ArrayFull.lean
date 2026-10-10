import Mathlib
import OAI.Probability.Ballisticity.Stationary.StationaryMonotone

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma arrayTransport_image {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e)
    (ho : ArrayOffsetsConsistent e Y) (hf : ∀ i, CurrentFiniteClasses e (arrayCurrentData e i Y))
    (hs : ∀ a, ∃ b, ArrayRelated e Y (i,a) (i+1,b))
    (hcard : (arrayClassFinset e (i+1) Y).card=(arrayClassFinset e i Y).card) :
    (arrayClassFinset e i Y).image (arrayTransport e i Y)=arrayClassFinset e (i+1) Y := by
  apply Finset.eq_of_subset_of_card_le
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    exact arrayTransport_mem e i Y (hf (i+1)) a
  · rw [Finset.card_image_iff.mpr (arrayTransport_injOn e i Y ho (hf i) hs),hcard]

lemma array_backward_survives {d : ℕ} (e : Direction d) (i : ℤ) (Y : ActualEpisodeArray e)
    (ho : ArrayOffsetsConsistent e Y) (hf : ∀ i, CurrentFiniteClasses e (arrayCurrentData e i Y))
    (hs : ∀ a, ∃ b, ArrayRelated e Y (i,a) (i+1,b))
    (hcard : (arrayClassFinset e (i+1) Y).card=(arrayClassFinset e i Y).card) (b : ℕ) :
    ∃ a, ArrayRelated e Y (i,a) (i+1,b) := by
  have hm : ReferenceClasses.representative (arrayCurrentData e (i+1) Y).1 b ∈
      arrayClassFinset e (i+1) Y := currentClassFinset_rep_mem e _ (hf (i+1)) b
  rw [←arrayTransport_image e i Y ho hf hs hcard] at hm
  obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp hm
  refine ⟨a,arrayRelated_trans e Y ho (arrayTransport_related e i Y ho a (hs a)) ?_⟩
  rw [heq]
  exact (arrayRelated_current e Y ho (i+1) _ _).mp (ReferenceClasses.representative_related _ b)

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma full_profiles (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) :
    ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event → ∀ i a z,
      0<(Y.2.2.1 (i,(i,a),z):ℝ) := by
  filter_upwards [L.consistent,L.sampling,L.elliptic,L.continuation,L.finite_marks,
    G.no_dust,L.finite_classes_all_times hue htrans G,L.class_card_constant hue htrans G]
    with Y hO hs he hc hm hd hf hcard hY i b z
  have hsurv (j : ℤ) := array_forward_survives e Y hs L.κ L.κ_pos he hc
    (fun j => ⟨(hm j).1,(hm j).2.1⟩) (hd hY) j
  obtain ⟨a,w,hw⟩ := array_backward_survives e (i-1) Y hO.1 (hf hY) (hsurv (i-1)) (hcard hY (i-1)) b
  have ha : 0<(Y.2.2.1 (i-1,(i-1,a),0):ℝ) :=
    lt_of_le_of_ne (Y.2.2.1 (i-1,(i-1,a),0)).property.1
      (show (Y.2.2.1 (i-1,(i-1,a),0):ℝ)≠0 from hd hY (i-1) a).symm
  have hp := array_next_full e Y L.κ L.κ_pos he hc
    (fun j => ⟨(hm j).1,(hm j).2.1⟩) (i-1) a ha (w+z)
  have hc' := hO.2.1 i (i-1,a) (i-1+1,b) w z hw
  simp only [sub_add_cancel] at hp hc'
  rwa [hc'] at hp

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
