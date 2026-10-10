import Mathlib
import OAI.Probability.Ballisticity.Estimates.LocalRadiusOrder
import OAI.Probability.Ballisticity.Crossings.BadCrossingLaw
import OAI.Probability.Ballisticity.Estimates.AllOffsetConsistency
import OAI.Probability.Ballisticity.Stationary.BadArraySampling

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma finite_translated_atoms_le_one {H : Type*} [AddCommGroup H]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : Measure H) [IsProbabilityMeasure μ] (v : H) (s : Finset H) :
    ∑ z∈s, (μ {v+z}).toReal ≤ 1 := by
  rw [←ENNReal.toReal_sum (fun z _ => measure_ne_top μ _)]
  have he : ∑ z∈s, μ {v+z}=μ (↑(s.image (fun z => v+z)):Set H) := by
    rw [←sum_measure_singleton]
    have hi : ∀ a∈s, ∀ b∈s, v+a=v+b → a=b := fun a _ b _ h => add_left_cancel h
    exact (Finset.sum_image (f := fun z => μ {z}) hi).symm
  rw [he]
  exact measureReal_le_one

def ArrayProfilesConsistent {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e) : Prop :=
  (∀ (j : ℤ) (p q : StationaryCompact.Label) (z w : HorizontalSpace e),
    Y.2.1 (p,q)=(z:OnePoint (HorizontalSpace e)) →
      Y.2.2.1 (j,p,z+w)=Y.2.2.1 (j,q,w)) ∧
  (∀ (j : ℤ) (p : StationaryCompact.Label) (s : Finset (HorizontalSpace e)),
    ∑ z∈s, (Y.2.2.1 (j,p,z):ℝ) ≤ 1)

lemma arrayProfilesConsistent_closed {d : ℕ} (e : Direction d) :
    IsClosed {Y : ActualEpisodeArray e | ArrayProfilesConsistent e Y} := by
  have ht : IsClosed {Y : ActualEpisodeArray e |
      ∀ (j : ℤ) (p q : StationaryCompact.Label) (z w : HorizontalSpace e),
      Y.2.1 (p,q)=(z:OnePoint (HorizontalSpace e)) →
        Y.2.2.1 (j,p,z+w)=Y.2.2.1 (j,q,w)} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun j => isClosed_iInter fun p => isClosed_iInter fun q =>
      isClosed_iInter fun z => isClosed_iInter fun w => ?_
    have heq : {Y : ActualEpisodeArray e | Y.2.1 (p,q)=(z:OnePoint (HorizontalSpace e)) →
        Y.2.2.1 (j,p,z+w)=Y.2.2.1 (j,q,w)} =
      {Y | Y.2.1 (p,q)=(z:OnePoint (HorizontalSpace e))}ᶜ ∪
      {Y | Y.2.2.1 (j,p,z+w)=Y.2.2.1 (j,q,w)} := by
      ext; simp [imp_iff_not_or]
    rw [heq]
    exact ((ReferenceClasses.finite_value_clopen z).preimage (by fun_prop)).2.isClosed_compl.union
      (isClosed_eq (by fun_prop) (by fun_prop))
  have hm : IsClosed {Y : ActualEpisodeArray e |
      ∀ (j : ℤ) (p : StationaryCompact.Label) (s : Finset (HorizontalSpace e)),
      ∑ z∈s, (Y.2.2.1 (j,p,z):ℝ) ≤ 1} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun j => isClosed_iInter fun p => isClosed_iInter fun s => ?_
    exact isClosed_le (by fun_prop) continuous_const
  exact ht.inter hm

lemma actual_arrayProfilesConsistent {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (X : EpisodeInput e) :
    ArrayProfilesConsistent e (actualArrayMap e t J X) := by
  constructor
  · intro j p q z w h
    have he : X.1.2 q-X.1.2 p=z := OnePoint.coe_injective h
    change globalHorizontalCoordinate e (t X.1.1 j) X.1.1 (X.1.2 p+(z+w)) =
      globalHorizontalCoordinate e (t X.1.1 j) X.1.1 (X.1.2 q+w)
    congr 1
    rw [←he]
    abel
  · intro j p s
    exact finite_translated_atoms_le_one (globalHorizontalProfile e (t X.1.1 j) X.1.1) (X.1.2 p) s

lemma arrayProfilesConsistent_shift {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayProfilesConsistent e Y) : ArrayProfilesConsistent e (StationaryCompact.shift Y) := by
  constructor
  · intro j p q z w ho
    exact h.1 (j+1) (p.1+1,p.2) (q.1+1,q.2) z w ho
  · intro j p s
    exact h.2 (j+1) (p.1+1,p.2) s

lemma actualOccupation_profilesConsistent {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) (N : ℕ) (M : Environment d → ℕ)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ) :
    ∀ᵐ Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)),
      ArrayProfilesConsistent e Y :=
  actualOccupation_ae_of_invariant e ν Q t J ht hJ N M hpos _
    (arrayProfilesConsistent_closed e).measurableSet (actual_arrayProfilesConsistent e t J)
    (arrayProfilesConsistent_shift e)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma array_offset_symm {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (h : ArrayOffsetsConsistent e Y) (p q : StationaryCompact.Label)
    (z : HorizontalSpace e) (ho : Y.2.1 (p,q)=(z:OnePoint (HorizontalSpace e))) :
    Y.2.1 (q,p)=((-z:HorizontalSpace e):OnePoint (HorizontalSpace e)) := by
  let E := Denumerable.eqv StationaryCompact.Label
  have hs := (h E.symm).symm (E p) (E q) z
  simpa only [selectedOffsets,Equiv.symm_apply_apply] using hs (by simpa [selectedOffsets] using ho)

lemma dust_isolated {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hO : ArrayOffsetsConsistent e Y) (hP : ArrayProfilesConsistent e Y)
    (hzero : ∀ p q z, p≠q → arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0)
    (p q : StationaryCompact.Label) (hpq : p≠q)
    (hdust : arrayProfileTest e p.1 p 0 Y=0) (z : HorizontalSpace e) :
    Y.2.1 (p,q)≠(z:OnePoint (HorizontalSpace e)) := by
  intro ho
  have hrev := array_offset_symm e Y hO p q z ho
  have hp := congrArg Subtype.val (hP.1 p.1 p q z (-z) ho)
  have hprofile : arrayProfileTest e p.1 q (-z) Y=0 := by
    change (Y.2.2.1 (p.1,q,-z)).val=0
    simp only [add_neg_cancel] at hp
    exact hp.symm.trans hdust
  have htest := hzero q p (-z) hpq.symm hprofile
  simp [arrayOffsetTest,finiteOffsetTest,hrev] at htest

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma bad_limit_consistent (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (Ns : ℕ → ℕ) (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
    ∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)),
      ArrayOffsetsConsistent e Y ∧ ArrayProfilesConsistent e Y := by
  have ho := closed_support_weak_limit _ ρ hlim _ (arrayOffsetsConsistent_closed e) (fun n =>
    actualOccupation_offsetsConsistent e ν _ (C.paddedTimes hef (Ns n)) (C.paddedStages hef (Ns n))
      (C.paddedTimes_measurable hef (Ns n)) (C.paddedStages_measurable hef (Ns n)) (Ns n)
      (C.activeCount hef (Ns n)) (C.bad_raw_mass_pos hef (Ns n) (hN n) (hmass n)))
  have hp := closed_support_weak_limit _ ρ hlim _ (arrayProfilesConsistent_closed e) (fun n =>
    actualOccupation_profilesConsistent e ν _ (C.paddedTimes hef (Ns n)) (C.paddedStages hef (Ns n))
      (C.paddedTimes_measurable hef (Ns n)) (C.paddedStages_measurable hef (Ns n)) (Ns n)
      (C.activeCount hef (Ns n)) (C.bad_raw_mass_pos hef (Ns n) (hN n) (hmass n)))
  filter_upwards [ho,hp] with Y hO hP
  exact ⟨hO,hP⟩

end OperationalConstants
end DirectionalTransience

end

end OAI
