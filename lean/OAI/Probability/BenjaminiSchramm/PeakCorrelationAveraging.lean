import OAI.Probability.BenjaminiSchramm.PeakClusterCorrelation
import OAI.Probability.BenjaminiSchramm.FreshSlabConcatenation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def connectionAvoidingHit (I J : Set E) (u w : V) (T : Set V) : Set (Set E) :=
  {ω | Conn G (ω ∩ J) u w ∧ ω ∉ restrictedHit G I u T}

omit [Countable V] [Countable E] in
lemma connectionAvoidingHit_finite_cells (I J : Set E) (hJI : J ⊆ I)
    (u w : V) (T : Set V) (ω : Set E) (hf : (cluster G (ω ∩ I) u).Finite) :
    ω ∈ connectionAvoidingHit G I J u w T ↔
      ∃ S : Finset V, ω ∈ peakConnectionCell G I J u w (S : Set V) T := by
  constructor
  · rintro ⟨hw,havoid⟩
    let S := hf.toFinset
    have hs : cluster G (ω ∩ I) u=(S : Set V) := hf.coe_toFinset.symm
    apply Exists.intro S
    apply (peakConnectionCell_iff G I J hJI u w _ T ω).mpr
    refine ⟨hs,hw,Set.disjoint_left.mpr ?_⟩
    intro v hv hvT
    apply havoid
    refine ⟨v,hvT,?_⟩
    change v ∈ cluster G (ω ∩ I) u
    rwa [hs]
  · rintro ⟨S,hS⟩
    obtain ⟨hs,hw,hdis⟩ := (peakConnectionCell_iff G I J hJI u w _ T ω).mp hS
    refine ⟨hw,?_⟩
    rintro ⟨v,hvT,huv⟩
    apply Set.disjoint_left.mp hdis _ hvT
    rw [←hs]
    exact huv

lemma measure_peakConnectionCell_partition (p : unitInterval)
    (I J : Set E) (hJI : J ⊆ I) (u w : V) (T : Set V)
    (hfin : ∀ᵐ ω ∂law p, (cluster G (ω ∩ I) u).Finite)
    (B : Set (Set E)) (hB : MeasurableSet B) :
    law p (connectionAvoidingHit G I J u w T ∩ B) =
      ∑' S : Finset V, law p (peakConnectionCell G I J u w (S : Set V) T ∩ B) := by
  have hdis : Pairwise (fun S U : Finset V => Disjoint
      (peakConnectionCell G I J u w (S : Set V) T ∩ B)
      (peakConnectionCell G I J u w (U : Set V) T ∩ B)) := by
    intro S U hne
    apply Set.disjoint_left.mpr
    rintro ω ⟨hS,_⟩ ⟨hU,_⟩
    exact hne (Finset.coe_injective (hS.1.symm.trans hU.1))
  calc
    _ = law p (⋃ S : Finset V, peakConnectionCell G I J u w (S : Set V) T ∩ B) := by
      apply measure_congr
      filter_upwards [hfin] with ω hω
      simp only [Set.mem_inter_iff,Set.mem_iUnion]
      rw [connectionAvoidingHit_finite_cells G I J hJI u w T ω hω]
      exact propext exists_and_right.symm
    _ = _ := measure_iUnion hdis fun S =>
      (measurableSet_peakConnectionCell G I J u w (S : Set V) T).inter hB

theorem connection_avoiding_hit_negative_correlation (p : unitInterval)
    (I J : Set E) (hJI : J ⊆ I) (u w : V) (A T : Set V)
    (hfin : ∀ᵐ ω ∂law p, (cluster G (ω ∩ I) u).Finite) :
    law p (connectionAvoidingHit G I J u w T ∩ restrictedSetHit G I A T) ≤
      law p (connectionAvoidingHit G I J u w T)*law p (restrictedSetHit G I A T) := by
  have hpart : law p (connectionAvoidingHit G I J u w T) =
      ∑' S : Finset V, law p (peakConnectionCell G I J u w (S : Set V) T) := by
    simpa only [Set.inter_univ] using measure_peakConnectionCell_partition G p I J hJI u w T hfin
      Set.univ MeasurableSet.univ
  rw [measure_peakConnectionCell_partition G p I J hJI u w T hfin
    (restrictedSetHit G I A T) (measurableSet_restrictedSetHit G I A T),hpart,
      ←ENNReal.tsum_mul_right]
  exact ENNReal.tsum_le_tsum fun S => peakConnectionCell_hit_probability G p I J u w _ A T

end Percolation.BenjaminiSchramm

end

end OAI
