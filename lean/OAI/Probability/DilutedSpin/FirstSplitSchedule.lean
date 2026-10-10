import OAI.Probability.DilutedSpin.ConditionalScheduledMean
import OAI.Probability.DilutedSpin.VertexContinuity

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

lemma realize_unary_of_later (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : ∀ v, d<q v) :
    realize (H+1) d S q=PrescribedTree.unary (realize H (d+1) S q) := by
  cases S with
  | leaf => rfl
  | node k hk C => rw [realize,ite_eq_left (hq none)]

/-- At the assigned first split, the whole scheduled mean is EXACTLY the
product of its proper-child means, including the transition at that split. -/
lemma conditionalScheduledMean_rootProduct (H p : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (q : (j : Fin k) → (C j).Vertex → ℕ)
    (hq : ∀ j v, p<q j v) (T : KernelTower Ω (H+1+p))
    (f : FinitePath Ω (H+1+p) → Fin N → ℝ) (x : FinitePath Ω (H+1+p)) (i : Fin N) :
    conditionalScheduledMean (H+1+p) 0 p (.node k hk C) (rootSchedule p q) T (fun y => f y i) x=
      conditionalScheduledProduct (H+1+p) 0 p C q T f x i := by
  rw [conditionalScheduledMean_eq_tail]
  simp only [Nat.zero_add,realize,rootSchedule,lt_self_iff_false,ite_false]
  rw [PrescribedTree.tailMean_node_product]
  unfold conditionalScheduledProduct
  apply Finset.prod_congr rfl
  intro j _
  rw [conditionalScheduledMean_eq_tail,Nat.zero_add,realize_unary_of_later H p (C j) (q j) (hq j)]

/-- Literal identification with the old/target projector in the matrix
identity, at arbitrary initial evaluation prefix and later first split. -/
lemma conditionalScheduledMean_eq_splitProjector (H r d a : ℕ) (S : ReducedTopology)
    (q : S.Vertex → ℕ) (T : KernelTower Ω (H+r+1+d))
    (f : FinitePath Ω (H+r+1+d) → ℝ) (x : FinitePath Ω (H+r+1+d)) :
    conditionalScheduledMean (H+r+1+d) a (r+1+d) S q T f x=
      PrescribedTree.splitProjector (realize H (a+(r+1+d)) S q) r d T f x := by
  induction d generalizing a with
  | zero => exact conditionalScheduledMean_eq_tail H (r+1) a S q T f x
  | succ d ih =>
    change conditionalScheduledMean (H+r+1+d) (a+1) (r+1+d) S q
      (T.2 x.1) (fun y => f (x.1,y)) x.2=_
    have h := ih (a+1) (T.2 x.1) (fun y => f (x.1,y)) x.2
    simpa only [PrescribedTree.splitProjector,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- The actual first-split projector in the matrix observable is precisely
the scheduled conditional child product. This applies to the old or delayed
target schedule separately, without altering any branching assignment. -/
theorem scheduled_splitProjector_product (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (q : (j : Fin k) → (C j).Vertex → ℕ)
    (hq : ∀ j v, r+1+d<q j v) (T : KernelTower Ω (H+1+r+1+d))
    (f : FinitePath Ω (H+1+r+1+d) → Fin N → ℝ) :
    (fun x i => PrescribedTree.splitProjector
      (realize (H+1) (r+1+d) (.node k hk C) (rootSchedule (r+1+d) q)) r d T (fun y => f y i) x)=
      conditionalScheduledProduct (H+1+r+1+d) 0 (r+1+d) C q T f := by
  funext x i
  simp only [realize,rootSchedule,lt_self_iff_false,ite_false]
  rw [PrescribedTree.splitProjector_node_product]
  unfold conditionalScheduledProduct
  apply Finset.prod_congr rfl
  intro j _
  have h := conditionalScheduledMean_eq_splitProjector (H+1) r d 0 (C j) (q j) T (fun y => f y i) x
  rw [Nat.zero_add,realize_unary_of_later H (r+1+d) (C j) (q j) (hq j)] at h
  exact h.symm

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
