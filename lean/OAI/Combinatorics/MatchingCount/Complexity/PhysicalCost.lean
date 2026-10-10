import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.Wrapper
import OAI.Combinatorics.MatchingCount.Complexity.OriginalCost

namespace OAI

namespace MatchingFPRAS.LiteralPhysical
open Polynomial PhysicalStream TreeTyped BitComplexity LiteralPacked

lemma polynomial_eval (p : Polynomial ℕ) : PolynomiallyBounded (fun x=>p.eval x) := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    simpa only [Polynomial.eval_add] using hp.add hq
  · intro n a
    simpa only [Polynomial.eval_monomial] using (PolynomiallyBounded.const a).mul (PolynomiallyBounded.id.pow n)
lemma polynomial_budget (w H : ℕ) {f g : ℕ→ℕ}
    (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun x=>LiteralBlockMap.budget w H (f x) (g x)) :=
  (hf.add (PolynomiallyBounded.const 1)).mul
    ((PolynomiallyBounded.const (3+w+H)).add ((PolynomiallyBounded.const 2).mul
      (hg.add (hf.mul (PolynomiallyBounded.const (H+w))))))
lemma polynomial_packTime {f : ℕ→ℕ} (hf : PolynomiallyBounded f) :
    PolynomiallyBounded (fun x=>packTime (f x)) :=
  ((PolynomiallyBounded.const 1).add (polynomial_budget 1 (18*width) hf (PolynomiallyBounded.const 0))).mul
    (PolynomiallyBounded.const (MachineCost.programCost packCode))
lemma polynomial_postTime {f : ℕ→ℕ} (hf : PolynomiallyBounded f) :
    PolynomiallyBounded (fun x=>postTime (f x)) :=
  (PolynomiallyBounded.const eraseTime).add
    (((PolynomiallyBounded.const 1).add (polynomial_budget (18*width) 1 hf (PolynomiallyBounded.const 0))).mul
      (PolynomiallyBounded.const (MachineCost.programCost unpackCode)))
lemma polynomial_factor {A B : Type} [Codec A] [Codec B] {f : A→Experiment B}
    (F : OnlineTree.Realizer f) {H n : ℕ→ℕ}
    (hH : PolynomiallyBounded H) (hn : PolynomiallyBounded n) :
    PolynomiallyBounded (fun x=>OnlineStack.Executes.factor F.program.code (H x) (n x)) := by
  let a:=OnlineStack.accesses F.program.code
  let o:=OnlineStack.overhead F.program.code
  exact ((PolynomiallyBounded.const o).mul ((PolynomiallyBounded.const 1).add
    ((PolynomiallyBounded.const (2*a)).mul ((hH.add (hn.mul (PolynomiallyBounded.const a))).add
      (PolynomiallyBounded.const 1))))).add (PolynomiallyBounded.const 1)

lemma mainTime_bound : ∃ C d : ℕ,0<C ∧ ∀ (G : GraphInput) (ε δ : ℚ),
    0<ε→ε<1→0≤δ→wrapTime LiteralAlgorithm.algorithmRealizer (encodeInput G ε δ)≤timeBound C d G ε δ := by
  obtain ⟨q,hq⟩:=LiteralAlgorithm.algorithm_bound
  let F:=LiteralAlgorithm.algorithmRealizer
  let bound:=fun x=>packTime x+q.eval x*OnlineStack.Executes.factor F.program.code (18*x+1) (q.eval x)+postTime (q.eval x)
  have hb : PolynomiallyBounded bound :=
    ((polynomial_packTime PolynomiallyBounded.id).add ((polynomial_eval q).mul
      (polynomial_factor F (((PolynomiallyBounded.const 18).mul PolynomiallyBounded.id).add
        (PolynomiallyBounded.const 1)) (polynomial_eval q)))).add (polynomial_postTime (polynomial_eval q))
  obtain ⟨C,d,hb⟩:=hb
  refine ⟨C+1,d,by omega,?_⟩
  intro G ε δ he he1 hd
  let as:=encodeInput G ε δ
  let x:=as.length+⌈ε⁻¹⌉₊+Nat.clog 2 ⌈δ⁻¹⌉₊+1
  have hx : 1≤x := by dsimp only [x];omega
  have hl : as.length≤x := by dsimp only [x];omega
  have hc := hq G ε δ he he1 hd x hx hl (by dsimp only [x];omega) (by dsimp only [x];omega)
  have hcost : F.cost as≤q.eval x := by dsimp only [F,as];omega
  have hout : (LiteralAlgorithm.algorithm as).worst weight≤q.eval x := by dsimp only [as];omega
  have hword : (LiteralAlgorithm.algorithm as).worst List.length≤q.eval x :=
    Experiment.worst_le _ _ _ ((Experiment.all_worst _ weight).mono (fun bs hbs=>
      (list_length_le_weight bs).trans (hbs.trans hout)))
  have hweight : weight as≤18*x+1 := by rw [LiteralCodec.weight_word];omega
  have hwrap : wrapTime F as≤bound x := by
    unfold wrapTime OnlineTree.physicalCost
    exact Nat.add_le_add (Nat.add_le_add (packTime_mono hl)
      (Nat.mul_le_mul hcost (OnlineStack.Executes.factor_mono _ _ _ _ hweight hcost))) (postTime_mono hword)
  apply hwrap.trans ((hb x hx).trans ?_)
  change C*x^d≤(C+1)*x^d
  exact Nat.mul_le_mul_right _ (by omega)
end MatchingFPRAS.LiteralPhysical

end OAI
