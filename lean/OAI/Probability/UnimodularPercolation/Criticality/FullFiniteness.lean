import Mathlib
import OAI.Probability.UnimodularPercolation.Main
import OAI.Probability.UnimodularPercolation.Criticality.ClusterCount
import OAI.Probability.UnimodularPercolation.Encounter.Surgery
import OAI.Probability.UnimodularPercolation.Encounter.ZeroIntensity

namespace OAI

/-! Almost-sure critical cluster finiteness from the full root transport. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory
universe u v w
variable {V : Type u} {E : Type v} {ι : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteOverwrite_preimage_zero [Countable E] (p : unitInterval)
    (hp : 0 < p) (hp1 : p < 1) (F P : Finset E) (hPF : P ⊆ F)
    (B : Set (Set E)) (hB : MeasurableSet B) (hz : law p B = 0) :
    law p ((finiteOverwrite F P) ⁻¹' B) = 0 := by
  by_contra hn
  have hpos := finiteOverwrite_pos p hp hp1 F P hPF
    ((finiteOverwrite F P) ⁻¹' B) B hB (pos_iff_ne_zero.mpr hn) (fun _ h => h)
  rw [hz] at hpos
  exact lt_irrefl _ hpos

theorem critical_finite_count_ae_of_transport [Infinite V] [Fintype ι]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 < weight i)
    (hw1 : ∑ i, weight i = 1)
    (hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x) :
    ∀ᵐ ω ∂law (pc G), (infiniteClusters G ω).Finite := by
  let : Countable V := countable_vertices hloc hconn
  let : Countable E := countable_edges hloc
  have hp := pc_pos G hloc hqt
  have hp1 := pc_lt_one_of_nonamenable G hconn hloc hqt hh
  have he (F P : Finset E) (x : V) :
      ∀ᵐ ω ∂law (pc G), P ⊆ F → ¬ IsEncounter G (finiteOverwrite F P ω) x := by
    by_cases hPF : P ⊆ F
    · have hz := finiteOverwrite_preimage_zero (pc G) hp hp1 F P hPF
        {ω | IsEncounter G ω x} (measurableSet_isEncounter G x)
        (critical_encounter_zero G hconn hloc hp root weight htr hw hw1 hcov x)
      apply ae_iff.mpr
      simpa only [hPF,true_implies,not_not,Set.preimage_ofPred_eq] using hz
    · filter_upwards [] with ω
      exact fun h => False.elim (hPF h)
  have hall : ∀ᵐ ω ∂law (pc G), ∀ F P : Finset E, ∀ x : V,
      P ⊆ F → ¬ IsEncounter G (finiteOverwrite F P ω) x :=
    ae_all_iff.mpr fun F => ae_all_iff.mpr fun P => ae_all_iff.mpr (he F P)
  filter_upwards [hall] with ω hω
  by_contra hinf
  obtain ⟨z,hz,hsep⟩ := three_of_infinite_count G ω hinf
  obtain ⟨F,P,hPF,x,hx⟩ := encounter_surgery_of_three G hconn hloc ω z hz hsep
  exact hω F P x hPF hx

theorem critical_finite_ae_of_transport [Infinite V] [Fintype ι]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 < weight i)
    (hw1 : ∑ i, weight i = 1)
    (hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x) :
    ∀ᵐ ω ∂law (pc G), ∀ x, (cluster G ω x).Finite := by
  filter_upwards [critical_finite_count_ae_of_transport G hconn hloc hqt hh
    root weight htr hw hw1 hcov,critical_finite_count_empty_ae G hconn hloc hqt hh] with ω hf he
  have hempty := he hf
  intro x
  by_contra hx
  have hc : cluster G ω x ∈ infiniteClusters G ω := ⟨hx,x,rfl⟩
  rw [hempty] at hc
  exact hc

end Percolation

end OAI
