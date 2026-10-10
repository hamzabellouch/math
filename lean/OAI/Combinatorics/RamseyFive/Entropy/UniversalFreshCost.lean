import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.UniversalReverse

namespace OAI


namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype B]

noncomputable def universalFreshCost (W : Finset B) (H : ℕ) (q : ℝ)
    (m : UniversalFreshMessage W H q) : ℝ :=
  Real.log (H+1:ℝ)+Real.log (W.card+1:ℝ)+
    Real.log (Fintype.card (Fin (cardCutoff q m.2.1 W.card m.1)):ℝ)

lemma universalFresh_headers (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (H : ℕ) (n : Fin (H+1)) (q M : ℝ)
    (t : UniversalFresh B H q) (m : UniversalFreshMessage W H q)
    (hm : universalFreshEncoded R S U C W hCW H n q M t=some m) :
    m.1=n ∧ m.2.1.val=C.card := by
  unfold universalFreshEncoded at hm
  split_ifs at hm with hW
  · obtain ⟨f,hf,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    refine ⟨rfl,?_⟩
    unfold freshEncoded at hf
    obtain ⟨i,hi,he⟩ := Option.map_eq_some_iff.mp hf
    exact congrArg (fun z : FreshMessage W n q=>z.1.val) he.symm

lemma universalFresh_cost_exact (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hCW : C⊆W) (H : ℕ) (n : Fin (H+1)) (q M : ℝ)
    (t : UniversalFresh B H q) (m : UniversalFreshMessage W H q)
    (hm : universalFreshEncoded R S U C W hCW H n q M t=some m) :
    universalFreshCost W H q m=Real.log (H+1:ℝ)+Real.log (W.card+1:ℝ)+
      Real.log (Fintype.card (Fin (cardCutoff q C.card W.card n)):ℝ) := by
  have hh := universalFresh_headers R S U C W hCW H n q M t m hm
  unfold universalFreshCost
  rw [hh.2,hh.1]
end SharpRamseyFive.ReverseCap

end OAI
