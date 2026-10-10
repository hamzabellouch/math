import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEvenTapeGeometry
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathPolynomialBound

namespace OAI

/-! The literal parity-correction tape retains the calibrated physical
coefficients and scalar offset, in its explicit triple-edge order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEvenTapeGeometry
open scoped BigOperators Classical

variable {G : QMARationalExchangeGraph} (P : QMAPlanarRouteData G)
    {m : ℕ} (labels : G.Edge ≃ Fin m) (N : ℚ)

private theorem packed_sum (f : ℚ → ℚ) :
    ((QuantumListGraph.packed G labels).map (fun e => f e.2.2)).sum =
      ∑ i : Fin (Finset.univ : Finset G.Edge).card,
        f (G.weight (QMAEvenRouteData.selected i)) := by
  simp only [QuantumListGraph.packed,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  have h := (QuantumEvenRouteLabels.activeIndex labels).sum_comp
    (fun i => f (G.weight (QMAEvenRouteData.selected i)))
  simpa only [QuantumEvenRouteLabels.selected_index] using h

theorem scale_eq :
    (QuantumListPathStep.parameters (QuantumEvenTapeProgram.stepInput (input P labels N))).2.2 =
      G.pathScale Finset.univ N := by
  let p := QuantumListPathStep.scaleInput (QuantumEvenTapeProgram.stepInput (input P labels N))
  have ha : QuantumPathScaleProgram.active p =
      3*(∑ i : Fin (Finset.univ : Finset G.Edge).card,
        (1+2*|G.weight (QMAEvenRouteData.selected i)|)) := by
    change 3*(((QuantumListGraph.packed G labels).map (fun e => e.2.2)).map
      QuantumPathScaleProgram.linearCost).sum = _
    rw [List.map_map]
    exact congrArg (fun z : ℚ => 3*z) (packed_sum labels (fun q => 1+2*|q|))
  have hb : QuantumPathScaleProgram.base p = |G.constant| := by
    change 3*(([] : List ℚ).map abs).sum+|G.constant| = _
    simp
  have hs : (p.2.2.map QuantumPathScaleProgram.squareCost).sum =
      ∑ i : Fin (Finset.univ : Finset G.Edge).card,
        (1+|G.weight (QMAEvenRouteData.selected i)|)^2 := by
    change (((QuantumListGraph.packed G labels).map (fun e => e.2.2)).map
      QuantumPathScaleProgram.squareCost).sum = _
    rw [List.map_map]
    exact packed_sum labels (fun q => (1+|q|)^2)
  change QuantumPathScaleProgram.value p = _
  unfold QuantumPathScaleProgram.value QuantumPathScaleProgram.correction
  rw [ha,hb,hs]
  simp only [QMARationalExchangeGraph.pathScale]
  have hz : (∑ e : {e : G.Edge // e ∉ (Finset.univ : Finset G.Edge)},
      |G.weight e.val|) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    exact (e.property (Finset.mem_univ _)).elim
  rw [hz]
  simp only [mul_zero,zero_add]
  rfl

theorem literal_weight (e : Fin (QuantumEvenTapeProgram.entries (input P labels N)).length) :
    (QuantumListSchedule.graph (QuantumEvenTapeProgram.value (input P labels N)).1
      (input_valid P labels N)).weight e =
      (P.toEven.schedule N).graph.weight (edge P labels N e) := by
  change ((QuantumEvenTapeProgram.entries (input P labels N)).get e).2.2.2 = _
  rw [entry_tag]
  change _ = (P.toEven.schedule N).graph.weight
    (QuantumEvenRouteLabels.edge labels (tripleEquiv P labels N e))
  generalize tripleEquiv P labels N e=t
  rcases t with ⟨i,k⟩
  change QuantumListPathProgram.coefficient
    (QuantumListSchedule.blockBondInput (QuantumEvenTapeProgram.blockInput
      (i.val,input P labels N))) k.castSucc = _
  rw [source_eq]
  unfold QuantumListPathProgram.coefficient
  rw [scale_eq]
  fin_cases k
  · rfl
  · rfl
  · change QuantumPathCode.coefficients (true,G.pathScale Finset.univ N,G.weight (labels.symm i)) 2 =
      QuantumPathCode.coefficients (true,G.pathScale Finset.univ N,
        G.weight (QMAEvenRouteData.selected (QuantumEvenRouteLabels.activeIndex labels i))) 2
    rw [QuantumEvenRouteLabels.selected_index]

theorem literal_constant :
    (QuantumListSchedule.graph (QuantumEvenTapeProgram.value (input P labels N)).1
      (input_valid P labels N)).constant = (P.toEven.schedule N).graph.constant := by
  change G.constant+QuantumListPathProgram.familyOffset
    (QuantumListPathStep.parameters (QuantumEvenTapeProgram.stepInput (input P labels N)),
      QuantumListGraph.packed G labels) = _
  unfold QuantumListPathProgram.familyOffset QuantumListPathProgram.offset
    QuantumListPathProgram.coefficient
  change G.constant+((QuantumListGraph.packed G labels).map
    (fun e => (3/4:ℚ)+3*e.2.2^2+3*(QuantumListPathStep.parameters
      (QuantumEvenTapeProgram.stepInput (input P labels N))).2.2^2)).sum = _
  rw [scale_eq]
  rw [packed_sum labels (fun q => (3/4:ℚ)+3*q^2+3*(G.pathScale Finset.univ N)^2),
    Finset.sum_add_distrib]
  simp only [Finset.sum_const,nsmul_eq_mul]
  have hcard : (Finset.univ : Finset (Fin (Finset.univ : Finset G.Edge).card)).card =
      (Finset.univ : Finset G.Edge).card :=
    (Finset.card_univ).trans (Fintype.card_fin _)
  rw [hcard]
  change G.constant+((∑ i : Fin (Finset.univ : Finset G.Edge).card,
    ((3/4:ℚ)+3*(G.weight (QMAEvenRouteData.selected i))^2))+
      (Finset.univ : Finset G.Edge).card*(3*(G.pathScale Finset.univ N)^2)) = _
  change _ = (G.constant+∑ i : Fin (Finset.univ : Finset G.Edge).card,
    ((3/4:ℚ)+3*(G.weight (QMAEvenRouteData.selected i))^2))+
      3*(Finset.univ : Finset G.Edge).card*(G.pathScale Finset.univ N)^2
  ring

theorem coefficientBound (hN : 0 ≤ N) {M L T : ℝ}
    (hm : (Fintype.card G.Edge:ℝ) ≤ M) (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : G.CoefficientBound L) :
    (QuantumListSchedule.graph (QuantumEvenTapeProgram.value (input P labels N)).1
      (input_valid P labels N)).CoefficientBound (qmaPathCoefficientBound M L T) := by
  have h := G.subdivide_coefficientBound Finset.univ (fun _ => true) hN hm hL hT hc
  exact ⟨(congrArg (fun q : ℚ => |(q:ℝ)|) (literal_constant P labels N)).le.trans h.1,
    fun e => (congrArg (fun q : ℚ => |(q:ℝ)|) (literal_weight P labels N e)).le.trans (h.2 _)⟩

end ContinuumCoulomb.QuantumEvenTapeGeometry

end

end OAI
