import OAI.Combinatorics.ParityLifts.BoolFold

namespace OAI

namespace ParityWL.Complexity

def RBEval (p : FCode) (x : DataTree) (R : ℝ) (y : DataTree) : Prop :=
  ∃ B : ℕ, BEval p x B y ∧ (B : ℝ)≤R

lemma BEval.real {p : FCode} {x y : DataTree} {B : ℕ} (h : BEval p x B y) :
    RBEval p x B y := ⟨B,h,le_rfl⟩

lemma RBEval.mono {p : FCode} {x y : DataTree} {R S : ℝ}
    (h : RBEval p x R y) (hrs : R≤S) : RBEval p x S y := by
  obtain ⟨B,hB,h⟩ := h
  exact ⟨B,hB,h.trans hrs⟩

lemma RBEval.nonneg {p : FCode} {x y : DataTree} {R : ℝ} (h : RBEval p x R y) : 0≤R := by
  obtain ⟨B,_,h⟩ := h
  exact (Nat.cast_nonneg B).trans h

lemma RBEval.seq {p q : FCode} {x y z : DataTree} {R S : ℝ}
    (h : RBEval p x R y) (hg : RBEval q y S z) : RBEval (.seq p q) x (R+S+1) z := by
  obtain ⟨B,hB,h⟩ := h
  obtain ⟨C,hC,hg⟩ := hg
  exact ⟨B+C+1,hB.seq hC,by push_cast; linarith⟩

lemma RBEval.ceil {p : FCode} {x y : DataTree} {R : ℝ} (h : RBEval p x R y) :
    BEval p x ⌈R⌉₊ y := by
  obtain ⟨B,hB,h⟩ := h
  exact hB.mono (by exact_mod_cast h.trans (Nat.le_ceil R))

lemma RBEval.any {α : Type} [TreeCodec α] (p : FCode) (P : α → Prop)
    (S : ℕ) (R : ℝ) (hR : 0≤R) (xs : List α)
    (hs : ∀ a∈xs,(treeEncode a).size≤S)
    (hb : ∀ a∈xs,∃ b,RBEval p (treeEncode a) R (treeEncode b) ∧ (b=true↔P a)) :
    ∃ b,RBEval p.any (treeEncode xs)
      (500*(xs.length+1 : ℝ)^2*(S+R+6)) (treeEncode b) ∧ (b=true↔∃ a∈xs,P a) := by
  obtain ⟨b,hb',he⟩ := BEval.any p P S ⌈R⌉₊ xs hs (by
    intro a ha
    obtain ⟨b,hb,he⟩ := hb a ha
    exact ⟨b,hb.ceil,he⟩)
  refine ⟨b,hb'.real.mono ?_,he⟩
  have hc := Nat.ceil_lt_add_one hR
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

lemma RBEval.simulation {M : Machine} {bs : List Bool} {s : ℕ} {b : Bool} {R : ℝ}
    (h : Emits M bs s b) (hs : (s : ℝ)≤R) :
    RBEval (simulationCode M) (treeEncode bs)
      (simulationCoefficient M*(bs.length+R+1 : ℝ)^simulationDegree) (treeEncode b) := by
  apply (simulation_run h).real.mono
  push_cast
  gcongr

lemma RBEval.decision {p : FCode} {bs : List Bool} {b : Bool} {R : ℝ}
    (h : RBEval p (treeEncode bs) R (treeEncode b)) :
    ∃ s, Emits p.decision bs s b ∧
      (s : ℝ)≤500*(p.factor+2 : ℝ)*(p.depth+2 : ℝ)*(R+1)^2+44*bs.length+20 := by
  obtain ⟨B,hB,h⟩ := h
  rw [treeEncode_bits] at hB
  obtain ⟨s,hs,he⟩ := hB.decision
  refine ⟨s,by cases b <;> simpa using he,?_⟩
  calc
    (s : ℝ) ≤ 500*(p.factor+2 : ℝ)*(p.depth+2 : ℝ)*(B+1 : ℝ)^2+44*bs.length+20 := by exact_mod_cast hs
    _ ≤ _ := by gcongr
end ParityWL.Complexity

end OAI
