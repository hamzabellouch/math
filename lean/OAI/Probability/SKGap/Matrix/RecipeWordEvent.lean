import Mathlib
import OAI.Probability.SKGap.Stability.OrdinaryClosure
import OAI.Probability.SKGap.Localization.MarkedDiagnostic

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial
variable {n : ℕ}
lemma pairControl_fold {τ : Type*} (xs : List τ) (f : τ→Pair n→Pair n) {A : ℝ} {L : ℕ}
    (hL : 1≤L) (hf : ∀t V,PairControl A L V→PairControl A L (f t V)) :
    PairControl A L (xs.foldr f zeroPair) := by
  induction xs with
  | nil=>exact zeroPair_control hL
  | cons t xs ih=>exact hf t _ ih

namespace OrdinaryData
variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

theorem markedRecipe_control (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ))
    (x : Spin n) (N L : ℕ) {A : ℝ} (hA : 1≤A)
    (hT : ∀l,(∀t∈((T l).words D.j).1,wordBounded A t.2 ∧ t.2.length≤L) ∧
      (∀t∈((T l).words D.j).2,wordBounded A t.2 ∧ t.2.length≤L))
    (hp : ∀a≤N,∀b i,|D.auxCoefficient a b x i|≤A) :
    ∀a≤N,PairControl A (L+2*a+2) (D.markedRecipe T x a) := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih=>
    intro ha
    rw [markedRecipe]
    apply pairControl_fold _ _ (by omega)
    intro t V hV
    cases t with
    | inl l=>exact smallBranch_control hA (by omega) D.j _ _ _ (hT l) hV
    | inr b=>exact boundedBranch_control (by omega) D.j _ (hp a ha b) _ _ (ih b b.isLt (b.isLt.le.trans ha)) hV

end OrdinaryData

def WordDiagramBound (J : Interaction n) (j A B : ℝ) (L : ℕ) : Prop :=
  ∀w:OrdinaryWord n,w.length≤L→wordBounded A w→
    SKGap.diagonalSeminorm (matrixWord J w-Matrix.diagonal (Diagram.prediction j w))≤B

namespace OrdinaryData
variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

theorem ordinary_word_closure (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ))
    (x : Spin n) (N L : ℕ) (c : LocalConstants) (h : LocalOrdinaryInput D T x N c)
    {M B Q : ℝ} (hM : 0≤M) (hB : 0≤B) (hQ : 0≤Q)
    (hm : ∀l,mass ((T l).words D.j).1≤Q ∧ mass ((T l).words D.j).2≤Q)
    (hT : ∀l,(∀t∈((T l).words D.j).1,wordBounded c.A t.2 ∧ t.2.length≤L) ∧
      (∀t∈((T l).words D.j).2,wordBounded c.A t.2 ∧ t.2.length≤L))
    (hw : WordTestBound D.J c.A M (2*N+3))
    (hd : WordDiagramBound D.J D.j c.A B (L+2*N+2)) :
    let W:=c.normBudget D.j (Fintype.card ι)
    let R:=errorBudget (|D.j| *c.A) (c.sourceCost D.j (Fintype.card ι) (Fintype.card σ))
      (c.fieldCost D.j (Fintype.card ι))
    let V:=traceBudget ((Fintype.card ι:ℝ)*((2+|D.j|)*Q)) (2+|D.j| *c.A) W
    ∀a≤N,SmallBound (D.source a) x (W a) ∧ SmallBound (D.auxiliary a) x (W a) ∧
      (∑i,|Primary.derivativeMatrix (D.source a) x i i|)≤V a*B+(R a).1*M ∧
      (∑i,|Primary.derivativeMatrix (D.auxiliary a) x i i|)≤V a*B+(R a).2*M := by
  apply D.ordinary_local_closure T x N c h hM hB hQ hm hw
  intro a ha d hdd
  have hc:=D.markedRecipe_control T x N L c.one_le_A hT h.auxValue a ha
  constructor
  · intro t ht
    have H:=(hc.1 t ht) d hdd
    exact hd _ (H.2.trans (by omega)) H.1
  · intro t ht
    have H:=(hc.2 t ht) d hdd
    exact hd _ (H.2.trans (by omega)) H.1

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
