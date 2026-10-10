import OAI.Combinatorics.ParityLifts.UniformLeaf

namespace OAI

namespace ParityWL.Complexity

def PolyProgram.bagParameter (c : Convention) : PolyProgram ℕ ℕ (ParityWL.bagParameter c) := by
  cases c with
  | joint => exact (((PolyProgram.id ℕ).pair (PolyProgram.const 1)).comp PolyProgram.natAdd)
  | separate => exact PolyProgram.id ℕ

noncomputable def TreeProgram.uniformLeafPair (c : Convention) :
    TreeProgram (ℕ × BitFormula) (ℕ × List Bool)
      (fun x => (x.1,Complexity.uniformLeafOutput (bagParameter c x.1) x.2)) :=
  (TreeProgram.fst ℕ BitFormula).pair
    ((((PolyProgram.fst ℕ BitFormula).comp (PolyProgram.bagParameter c)).pair
      (PolyProgram.snd ℕ BitFormula)).program.comp TreeProgram.uniformLeafOutput)

noncomputable def PolyProgram.withDimension : PolyProgram (ℕ × List Bool) (List Bool)
    (fun x => Complexity.encodeNat x.1++x.2) :=
  ((((PolyProgram.fst ℕ (List Bool)).comp PolyProgram.encodeNat).pair
    (PolyProgram.snd ℕ (List Bool))).comp (PolyProgram.append Bool))

noncomputable def TreeProgram.uniformWLInput (c : Convention) :
    TreeProgram (ℕ × BitFormula) (List Bool)
      (fun x => Complexity.encodeNat x.1++Complexity.uniformLeafOutput (bagParameter c x.1) x.2) :=
  (TreeProgram.uniformLeafPair c).comp PolyProgram.withDimension.program

noncomputable def uniformLeafDecisionCode (c : Convention) (M : Machine) : FCode :=
  .seq (TreeProgram.uniformWLInput c).code (.seq (simulationCode M) PolyProgram.not.program.code)

noncomputable def uniformLeafTime (c : Convention) (k : ℕ) (F : BitFormula) : ℕ :=
  (TreeProgram.uniformWLInput c).time (k,F)

noncomputable def uniformLeafCost (c : Convention) (k : ℕ) (M : Machine) (C r : ℝ) (F : BitFormula) : ℝ :=
  uniformLeafTime c k F+simulationCoefficient M*(uniformLeafTime c k F+C*2^(r*leafWords (bagParameter c k) F)+1)^simulationDegree+negateCost+2

lemma uniformLeafMachine_run (k : ℕ) (hk : 4≤k) (c : Convention)
    (i : Implementation) (M : Machine) (f g : ℕ → ℝ)
    (hm : UniformWLBound M c i f g) :
    ∃ C : ℝ, 0<C ∧ ∀ F : BitFormula, (∀ D∈F,D.length≤3) →
      ∃ b,RBEval (uniformLeafDecisionCode c M) (treeEncode (k,F))
        (uniformLeafCost c k M C (g k) F) (treeEncode b) ∧
        (b=true↔∃ a,bitSat a F) := by
  let t := bagParameter c k
  let C := f k*(2*(orderFactor t+1 : ℝ))^(g k)
  refine ⟨C,by dsimp [C]; exact mul_pos (hm.1 k) (Real.rpow_pos_of_pos (by positivity) _),?_⟩
  intro F hw
  obtain ⟨n,G,H,he,hg,hn⟩ := uniformLeafOutput_spec k hk c F hw
  obtain ⟨s,b,hs,hb,hcost⟩ := hm.2.2 k hk n G H
  rw [←he] at hs
  have htime : (s : ℝ)≤C*2^((g k)*leafWords t F) := by
    apply hcost.trans
    have h := power_order_bound n (leafWords t F) (orderFactor t) (g k) (hm.2.1 k) hn
    dsimp only [C]
    nlinarith [mul_le_mul_of_nonneg_left h (hm.1 k).le]
  refine ⟨!b,?_,?_⟩
  · exact simulation_after (TreeProgram.uniformWLInput c) (k,F) hs htime
  · have hh := hb.trans (hg i)
    cases b <;> simp_all

end ParityWL.Complexity

end OAI
