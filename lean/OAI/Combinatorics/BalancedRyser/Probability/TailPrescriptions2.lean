import OAI.Combinatorics.BalancedRyser.Probability.TailConditioning2
import OAI.Combinatorics.BalancedRyser.Probability.TailPrescriptions

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Balanced.TailConditioning

universe u v w
variable {I : Type u} {Q : I → Type v} {V : Type w}

theorem ambientCylinder_eq_cylinder_of_mem
    (embed : ∀ i, Q i → V) (hinj : ∀ i, Function.Injective (embed i))
    (J : Finset I) (a : I → V) (b : Slots.Assignment Q)
    (hb : b ∈ ambientCylinder Q embed J a) :
    ambientCylinder Q embed J a = Slots.cylinder Q J b := by
  ext ω
  constructor
  · intro h i hi
    exact hinj i ((h i hi).trans (hb i hi).symm)
  · intro h i hi
    rw [h i hi]
    exact hb i hi

theorem ambientCylinder_eq_empty_of_unavailable
    (embed : ∀ i, Q i → V) (J : Finset I) (a : I → V)
    (hbad : ∃ i ∈ J, a i ∉ Set.range (embed i)) :
    ambientCylinder Q embed J a = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ω hω
  obtain ⟨i, hi, hbad⟩ := hbad
  exact hbad ⟨ω i, hω i hi⟩

theorem conditionalAmbientCylinder_eq_zero
    [Fintype I] [∀ i, Fintype (Q i)] [∀ i, MeasurableSpace (Q i)]
    (G : SimpleGraph (Sigma Q)) (embed : ∀ i, Q i → V)
    (J : Finset I) (a : I → V)
    (hbad : Disjoint (ambientCylinder Q embed J a) (independentTransversals Q G)) :
    conditionalAmbientCylinder Q G embed J a = 0 := by
  simp [conditionalAmbientCylinder, Set.disjoint_iff_inter_eq_empty.mp hbad]

theorem conditionalAmbientCylinder_eq_zero_of_unavailable
    [Fintype I] [∀ i, Fintype (Q i)] [∀ i, MeasurableSpace (Q i)]
    (G : SimpleGraph (Sigma Q)) (embed : ∀ i, Q i → V)
    (J : Finset I) (a : I → V)
    (hbad : ∃ i ∈ J, a i ∉ Set.range (embed i)) :
    conditionalAmbientCylinder Q G embed J a = 0 := by
  simp [conditionalAmbientCylinder, ambientCylinder_eq_empty_of_unavailable embed J a hbad]

theorem tail_conditioning_ambient
    [Fintype I] [∀ i, Fintype (Q i)]
    [∀ i, MeasurableSpace (Q i)] [∀ i, MeasurableSingletonClass (Q i)]
    (G : SimpleGraph (Sigma Q)) [DecidableRel G.Adj]
    (hno : TailGraph.NoWithinSlotEdges G Sigma.fst)
    (hmin : 3 ≤ minSlotSize Q)
    (hsparse : (G.maxDegree : ℝ) / minSlotSize Q ≤ 1 / 8)
    (embed : ∀ i, Q i → V) (hinj : ∀ i, Function.Injective (embed i)) :
    0 < (Slots.law Q).real (independentTransversals Q G) ∧
      ∀ (J : Finset I) (a : I → V),
        conditionalAmbientCylinder Q G embed J a ≤
          Real.exp ((J.card : ℝ) / 2) * ∏ i ∈ J, (Fintype.card (Q i) : ℝ)⁻¹ := by
  classical
  obtain ⟨hpos, hbound⟩ := tail_conditioning G hno hmin hsparse
  refine ⟨hpos, ?_⟩
  intro J a
  by_cases hne : (ambientCylinder Q embed J a).Nonempty
  · obtain ⟨b, hb⟩ := hne
    have heq := ambientCylinder_eq_cylinder_of_mem embed hinj J a b hb
    simpa only [conditionalAmbientCylinder, conditionalCylinder, heq] using hbound J b
  · have heq : ambientCylinder Q embed J a = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [conditionalAmbientCylinder, heq, Set.empty_inter, measureReal_empty,
      zero_div]
    positivity

end Balanced.TailConditioning

end OAI
