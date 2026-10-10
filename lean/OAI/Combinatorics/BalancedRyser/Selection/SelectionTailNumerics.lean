import OAI.Combinatorics.BalancedRyser.Probability.TailPrescriptions2
import OAI.Combinatorics.BalancedRyser.Selection.SelectionFinalLaw

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Balanced.TailConditioning

theorem tail_conditioning_ambient_of_pointwise_bounds
    {I V : Type*} {Q : I → Type*} [Fintype I] [∀ i, Fintype (Q i)]
    [∀ i, MeasurableSpace (Q i)] [∀ i, MeasurableSingletonClass (Q i)]
    (G : SimpleGraph (Sigma Q)) [DecidableRel G.Adj]
    (hno : TailGraph.NoWithinSlotEdges G Sigma.fst)
    (hsize : ∀ i, 3 ≤ Fintype.card (Q i))
    (hdegree : ∀ v i, 8 * G.degree v ≤ Fintype.card (Q i))
    (embed : ∀ i, Q i → V) (hinj : ∀ i, Function.Injective (embed i)) :
    0 < (Slots.law Q).real (independentTransversals Q G) ∧
      ∀ (J : Finset I) (a : I → V),
        conditionalAmbientCylinder Q G embed J a ≤
          Real.exp ((J.card : ℝ) / 2) * ∏ i ∈ J, (Fintype.card (Q i) : ℝ)⁻¹ := by
  classical
  obtain ⟨hpos, hbound⟩ := tail_conditioning_of_pointwise_bounds G hno hsize hdegree
  refine ⟨hpos, ?_⟩
  intro J a
  by_cases hne : (ambientCylinder Q embed J a).Nonempty
  · obtain ⟨b, hb⟩ := hne
    have heq := ambientCylinder_eq_cylinder_of_mem embed hinj J a b hb
    simpa only [conditionalAmbientCylinder, conditionalCylinder, heq] using hbound J b
  · have heq := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [conditionalAmbientCylinder, heq, Set.empty_inter, measureReal_empty, zero_div]
    positivity

end Balanced.TailConditioning

namespace Balanced.Selection.Process.Tail

noncomputable section

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] in
theorem conditionalAmbientCylinder_le_of_tailCheck
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (G : Input I V) (S : State I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (ht : TailCheck G S) (J : Finset (Slot S)) (a : Slot S → V) :
    TailConditioning.conditionalAmbientCylinder (Domain G S) (graph G S)
      (fun _ v => v.1) J a ≤
        Real.exp ((J.card : ℝ) / 2) *
          ∏ i ∈ J, ((domain G S i.1).card : ℝ)⁻¹ := by
  classical
  obtain ⟨hs, hd⟩ := (tailCheck_iff G S).mp ht
  have h := TailConditioning.tail_conditioning_ambient_of_pointwise_bounds
    (graph G S) (noWithinSlotEdges G S hno)
    (fun i => by simpa only [card_domain] using hs i.1 i.2)
    (fun v i => by
      rw [card_domain]
      exact (Nat.mul_le_mul_left 8 (degree_le G S v)).trans
        (hd _ (value_mem_current G S v) i.1 i.2))
    (fun _ v => v.1) (fun _ => Subtype.val_injective)
  simpa only [card_domain] using h.2 J a

end
end Balanced.Selection.Process.Tail

end OAI
