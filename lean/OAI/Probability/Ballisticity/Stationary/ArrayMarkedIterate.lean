import Mathlib
import OAI.Probability.Ballisticity.Stationary.StationaryMarking

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma markedShift_iterate_fst {d : ℕ} (e : Direction d) (p : MarkedArray e) (n : ℕ) :
    ((markedShift e)^[n] p).1=StationaryCompact.shift^[n] p.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    change StationaryCompact.shift ((markedShift e)^[n] p).1=_
    rw [ih]

lemma arrayOffset_iterate {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (n : ℕ) (p q : StationaryCompact.Label) :
    (StationaryCompact.shift^[n] Y).2.1 (p,q)=Y.2.1 ((p.1+n,p.2),(q.1+n,q.2)) := by
  induction n generalizing p q with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (StationaryCompact.shift^[n] Y).2.1 ((p.1+1,p.2),(q.1+1,q.2))=_
    rw [ih]
    simp only [Nat.cast_add,Nat.cast_one,add_left_comm,add_comm]

lemma arrayProfile_iterate {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (n : ℕ) (j : ℤ) (p : StationaryCompact.Label) (z : HorizontalSpace e) :
    (StationaryCompact.shift^[n] Y).2.2.1 (j,p,z)=Y.2.2.1 (j+n,(p.1+n,p.2),z) := by
  induction n generalizing j p with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (StationaryCompact.shift^[n] Y).2.2.1 (j+1,(p.1+1,p.2),z)=_
    rw [ih]
    simp only [Nat.cast_add,Nat.cast_one,add_left_comm,add_comm]

lemma marked_related_iterate {d : ℕ} (e : Direction d) (p : MarkedArray e)
    (ho : ArrayOffsetsConsistent e p.1)
    (hs : ∀ n, ArrayRelated e ((markedShift e)^[n] p).1 (0,((markedShift e)^[n] p).2)
      (1,((markedShift e)^[n+1] p).2)) (n : ℕ) :
    ArrayRelated e p.1 (0,p.2) (n,((markedShift e)^[n] p).2) := by
  induction n with
  | zero => exact arrayRelated_refl e p.1 ho _
  | succ n ih =>
    apply arrayRelated_trans e p.1 ho ih
    obtain ⟨z,hz⟩ := hs n
    rw [markedShift_iterate_fst,arrayOffset_iterate] at hz
    refine ⟨z,?_⟩
    simpa only [zero_add,add_zero,Nat.cast_add,Nat.cast_one,add_comm] using hz

noncomputable def markedDisplacement {d : ℕ} (e : Direction d) (n : ℕ) (p : MarkedArray e) : HorizontalSpace e :=
  if h : ArrayRelated e p.1 (0,p.2) (n,((markedShift e)^[n] p).2) then Classical.choose h else 0

lemma markedDisplacement_spec {d : ℕ} (e : Direction d) (n : ℕ) (p : MarkedArray e)
    (h : ArrayRelated e p.1 (0,p.2) (n,((markedShift e)^[n] p).2)) :
    p.1.2.1 ((0,p.2),(n,((markedShift e)^[n] p).2))=(markedDisplacement e n p : OnePoint (HorizontalSpace e)) := by
  rw [markedDisplacement,dite_eq_left h]
  exact Classical.choose_spec h

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma marked_related (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) :
    ∀ᵐ p ∂markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event,
      ∀ n : ℕ, ArrayRelated e p.1 (0,p.2) (n,((markedShift e)^[n] p).2) := by
  have h0 := markedArrayLaw_ae e (L.law : Measure (ActualEpisodeArray e)) G.event G.measurable_event
    (show ∀ᵐ Y ∂(L.law : Measure (ActualEpisodeArray e)), Y∈G.event →
      ArrayOffsetsConsistent e Y ∧ ∀ a, ArrayRelated e Y (0,a) (1,arrayTransport e 0 Y a) from by
      filter_upwards [L.consistent,L.sampling,L.elliptic,L.continuation,L.finite_marks,G.no_dust]
        with Y hO hs he hc hm hd hY
      refine ⟨hO.1,fun a => arrayTransport_related e 0 Y hO.1 a ?_⟩
      exact array_forward_survives e Y hs L.κ L.κ_pos he hc
        (fun i => ⟨(hm i).1,(hm i).2.1⟩) (hd hY) 0 a)
  have hall := ae_all_iff.mpr fun n =>
    ((L.marked_preserving hue htrans G).iterate n).quasiMeasurePreserving.ae h0
  filter_upwards [h0,hall] with p hp hh n
  apply marked_related_iterate e p hp.1 _ n
  intro k
  simpa only [Function.iterate_succ_apply',markedShift] using (hh k).2 ((markedShift e)^[k] p).2

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
