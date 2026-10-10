import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListScheduleGeometry

namespace OAI

/-! Exact calibration equality between the literal selected-weight sums and
the finite graph's rational subdivision scale. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open scoped BigOperators Classical

private theorem univ_eq {α : Type} (a b : Fintype α) :
    @Finset.univ α a = @Finset.univ α b :=
  congrArg (fun i : Fintype α => @Finset.univ α i) (Subsingleton.elim a b)

theorem partition_sum (b : Bool) (xs : List Entry) (f : Entry → ℚ) :
    ((partition b xs).map f).sum = ∑ i : Fin (partition b xs).length, f ((partition b xs).get i) := by
  have h : List.ofFn (fun i => f ((partition b xs).get i))=(partition b xs).map f := by
    simpa only [List.get_eq_getElem] using List.ofFn_getElem_eq_map (partition b xs) f
  rw [← h,List.sum_ofFn]

theorem active_sum (s : State) (hs : Valid s) (f : Entry → ℚ) :
    (∑ i : Fin (partition true s.2.2).length, f ((partition true s.2.2).get i)) =
      ∑ j : Fin (schedule s hs).active.card,
        f (s.2.2.get (qmaSelectedIndex (schedule s hs).active j)) := by
  have h := (activePermutation s hs).sum_comp
    (fun j => f (s.2.2.get (qmaSelectedIndex (schedule s hs).active j)))
  simpa only [active_source] using h

theorem retained_sum (s : State) (hs : Valid s) (f : Entry → ℚ) :
    (∑ i : Fin (partition false s.2.2).length, f ((partition false s.2.2).get i)) =
      ∑ j : {j : (graph s hs).Edge // j ∉ (schedule s hs).active}, f (s.2.2.get j.val) := by
  have h := (retainedEquiv s hs).sum_comp (fun j => f (s.2.2.get j.val))
  simpa only [retained_source] using h

theorem scale_eq (N : ℚ) (s : State) (hs : Valid s) :
    (QuantumListPathStep.parameters (stepInput (N,s))).2.2 =
      (graph s hs).pathScale (schedule s hs).active N := by
  let S := (schedule s hs).active
  let p := QuantumListPathStep.scaleInput (stepInput (N,s))
  let A : ℚ := 3*(∑ j : Fin S.card, (1+2*|(graph s hs).weight (qmaSelectedIndex S j)|))
  let B : ℚ := 3*(∑ j : {j : (graph s hs).Edge // j ∉ S}, |(graph s hs).weight j.val|)+|(graph s hs).constant|
  let D : ℚ := B+4*(∑ j : Fin S.card, (1+|(graph s hs).weight (qmaSelectedIndex S j)|)^2)
  have ha : QuantumPathScaleProgram.active p=A := by
    have h := congrArg (fun z : ℚ => 3*z)
      ((partition_sum true s.2.2 (fun e => 1+2*|e.2.2.2|)).trans
        (active_sum s hs (fun e => 1+2*|e.2.2.2|)))
    simpa only [A,S,graph,QuantumPathScaleProgram.active,p,QuantumListPathStep.scaleInput,stepInput,
      erase,List.map_map,Function.comp_def,QuantumPathScaleProgram.linearCost] using h
  have hb : QuantumPathScaleProgram.base p=B := by
    have h := congrArg (fun z : ℚ => 3*z+|s.2.1|)
      ((partition_sum false s.2.2 (fun e => |e.2.2.2|)).trans
        (retained_sum s hs (fun e => |e.2.2.2|)))
    simpa only [B,S,graph,QuantumPathScaleProgram.base,p,QuantumListPathStep.scaleInput,stepInput,
      erase,List.map_map,Function.comp_def] using h
  have hsq : (p.2.2.map QuantumPathScaleProgram.squareCost).sum =
      ∑ j : Fin S.card, (1+|(graph s hs).weight (qmaSelectedIndex S j)|)^2 := by
    have h := (partition_sum true s.2.2 (fun e => (1+|e.2.2.2|)^2)).trans
      (active_sum s hs (fun e => (1+|e.2.2.2|)^2))
    simpa only [S,graph,p,QuantumListPathStep.scaleInput,stepInput,erase,List.map_map,
      Function.comp_def,QuantumPathScaleProgram.squareCost] using h
  have hd : QuantumPathScaleProgram.correction p=D := by
    change QuantumPathScaleProgram.base p+4*(p.2.2.map QuantumPathScaleProgram.squareCost).sum=D
    rw [hb,hsq]
  change QuantumPathScaleProgram.value p = _
  unfold QuantumPathScaleProgram.value
  rw [ha,hd]
  simp only [A,B,D,S,p,QuantumListPathStep.scaleInput,stepInput,
    QMARationalExchangeGraph.pathScale,graph]
  congr!
  all_goals first | (cases ‹HEq _ _›; rfl) | apply univ_eq

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
