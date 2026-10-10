import OAI.Combinatorics.ParityLifts.RealEval

namespace OAI

namespace ParityWL.Complexity

noncomputable def leafDecisionCode (t : ℕ) [NeZero t] (M : Machine) : FCode :=
  .seq (TreeProgram.leafOutput t (Nat.pos_of_neZero t)).code
    (.seq (simulationCode M) PolyProgram.not.program.code)

def negateCost : ℕ := PolyProgram.not.program.time false+PolyProgram.not.program.time true+1

lemma negate_cost (b : Bool) : PolyProgram.not.program.time b≤negateCost := by
  cases b <;> dsimp only [negateCost] <;> omega

noncomputable def leafTime (t : ℕ) [NeZero t] (F : BitFormula) : ℕ :=
  (TreeProgram.leafOutput t (Nat.pos_of_neZero t)).time F

noncomputable def leafCost (t : ℕ) [NeZero t] (M : Machine) (C r : ℝ) (F : BitFormula) : ℝ :=
  leafTime t F+simulationCoefficient M*(leafTime t F+C*2^(r*leafWords t F)+1)^simulationDegree+negateCost+2

lemma power_order_bound (n q m : ℕ) (r : ℝ) (hr : 0≤r)
    (hn : n≤(2^q+1)*m) :
    (n+1 : ℝ)^r≤(2*(m+1 : ℝ))^r*2^(r*q) := by
  have hq : (1 : ℝ)≤(2 : ℝ)^q := one_le_pow₀ (by norm_num)
  have hn' : (n : ℝ)≤((2 : ℝ)^q+1)*m := by exact_mod_cast hn
  have hh : (n+1 : ℝ)≤2*(m+1 : ℝ)*(2 : ℝ)^q := by
    have hm := Nat.cast_nonneg (α:=ℝ) m
    nlinarith
  calc
    (n+1 : ℝ)^r ≤ (2*(m+1 : ℝ)*(2 : ℝ)^q)^r := Real.rpow_le_rpow (by positivity) hh hr
    _ = (2*(m+1 : ℝ))^r*((2 : ℝ)^q)^r := Real.mul_rpow (by positivity) (by positivity)
    _ = _ := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]
      rw [mul_comm (q : ℝ) r]

lemma TreeProgram.output_length {α β : Type} [TreeCodec α] [TreeCodec β]
    {f : α → List β} (P : TreeProgram α (List β) f) (x : α) :
    (f x).length ≤ P.time x := by
  have h := (treeEncode_list_length (f x)).trans (P.run x).bounds.2.1
  omega

lemma simulation_after {α : Type} [TreeCodec α] {f : α → List Bool}
    (P : TreeProgram α (List Bool) f) (x : α) {M : Machine} {s : ℕ} {b : Bool}
    {R : ℝ} (hs : Emits M (f x) s b) (hr : (s : ℝ) ≤ R) :
    RBEval (.seq P.code (.seq (simulationCode M) PolyProgram.not.program.code))
      (treeEncode x)
      (P.time x+simulationCoefficient M*(P.time x+R+1 : ℝ)^simulationDegree+negateCost+2)
      (treeEncode (!b)) := by
  have hp := P.run x
  have hlen : ((f x).length : ℝ) ≤ P.time x := by exact_mod_cast P.output_length x
  have hsim := RBEval.simulation hs hr
  have hnot := (PolyProgram.not.program.run b).real.mono
    (show (PolyProgram.not.program.time b : ℝ) ≤ negateCost by exact_mod_cast negate_cost b)
  apply (hp.real.seq (hsim.seq hnot)).mono
  have hbase : 0 ≤ ((f x).length : ℝ)+R+1 := by
    have := (Nat.cast_nonneg (α:=ℝ) s).trans hr
    positivity
  have hpow := pow_le_pow_left₀ hbase (show ((f x).length : ℝ)+R+1 ≤ P.time x+R+1 by linarith) simulationDegree
  nlinarith [mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (simulationCoefficient M))]

lemma leafDecision_eval (t : ℕ) [NeZero t] (F : BitFormula) {M : Machine}
    {s : ℕ} {b : Bool} {C r : ℝ}
    (hs : Emits M (leafOutput t F) s b) (ht : (s : ℝ) ≤ C*2^(r*leafWords t F)) :
    RBEval (leafDecisionCode t M) (treeEncode F) (leafCost t M C r F) (treeEncode (!b)) := by
  unfold leafDecisionCode leafCost leafTime
  exact simulation_after (TreeProgram.leafOutput t (Nat.pos_of_neZero t)) F hs ht

lemma leafMachine_run (k : ℕ) (hk : 4≤k) (c : Convention)
    [NeZero (bagParameter c k)] (i : Implementation) (M : Machine) (r : ℝ)
    (hr : 0≤r) (hm : FixedWLBound M c i k r) :
    ∃ C : ℝ, 0<C ∧ ∀ F : BitFormula, (∀ D∈F,D.length≤3) →
      ∃ b,RBEval (leafDecisionCode (bagParameter c k) M) (treeEncode F)
        (leafCost (bagParameter c k) M C r F) (treeEncode b) ∧
        (b=true↔∃ a,bitSat a F) := by
  obtain ⟨A,hA,hm⟩ := hm
  let t := bagParameter c k
  let C := A*(2*(orderFactor t+1 : ℝ))^r
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro F hw
  obtain ⟨n,G,H,he,hg,hn⟩ := leafOutput_spec k hk c F hw
  obtain ⟨s,b,hs,hb,hcost⟩ := hm n G H
  rw [←he] at hs
  have htime : (s : ℝ)≤C*2^(r*leafWords t F) := by
    apply hcost.trans
    have h := power_order_bound n (leafWords t F) (orderFactor t) r hr hn
    dsimp only [C]
    nlinarith [mul_le_mul_of_nonneg_left h hA.le]
  refine ⟨!b,?_,?_⟩
  · exact leafDecision_eval t F hs htime
  · have hh := hb.trans (hg i)
    cases b <;> simp_all
end ParityWL.Complexity

end OAI
