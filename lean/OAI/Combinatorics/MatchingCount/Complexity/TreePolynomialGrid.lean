import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.TreePolyTactic
import OAI.Combinatorics.MatchingCount.Complexity.TreeCostMeasure

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B : Type} [Codec A] [Codec B]
lemma weight_fst (a : A×B) : weight a.1≤weight a := by rcases a with ⟨a,b⟩; simp only [weight_prod]; omega
lemma weight_snd (a : A×B) : weight a.2≤weight a := by rcases a with ⟨a,b⟩; simp only [weight_prod]; omega

variable {m n : A → ℕ} {f : A×(ℕ×ℕ) → B}
def grid (M : Realizer m) (N : Realizer n) (F : Realizer f) :
    Realizer (fun a=>ExecutableDP.tabulate f (a,(m a,n a))) := by
  let rowF : Realizer (fun x : (A×ℕ)×ℕ=>f (x.1.1,(x.1.2,x.2))) :=
    composition (pair first.fst (pair first.snd second)) F
  let row : Realizer (fun x : A×ℕ=>(List.range (n x.1+1)).map fun r=>f (x.1,(x.2,r))) :=
    composition (pair identity (composition (composition (composition first N) successor) range)) (mapWith rowF)
  exact composition (pair identity (composition M range)) (mapWith row)
lemma polynomial_grid {M : Realizer m} {N : Realizer n} {F : Realizer f}
    (hM : PolynomialTime M) (hN : PolynomialTime N) (hF : PolynomialTime F)
    (p q : Polynomial ℕ) (hm : ∀ a,m a≤p.eval (weight a)) (hn : ∀ a,n a≤q.eval (weight a)) :
    PolynomialTime (grid M N F) := by
  have hrows : PolynomialTime (composition (composition (composition (first (A:=A) (B:=ℕ)) N) successor) range) := by
    apply polynomial_boundedRange (polynomial_composition (polynomial_composition polynomial_first hN) polynomial_successor) (q+1)
    intro x
    have hb:=(hn x.1).trans (polynomial_eval_monotone q (weight_fst x))
    simpa only [Function.comp_apply,Polynomial.eval_add,Polynomial.eval_one] using Nat.add_le_add_right hb 1
  unfold grid
  dsimp only
  apply polynomial_composition (polynomial_pair polynomial_identity (polynomial_boundedRange hM p hm))
  apply polynomial_mapWith
  apply polynomial_composition (polynomial_pair polynomial_identity hrows)
  apply polynomial_mapWith
  apply polynomial_composition _ hF
  exact polynomial_pair (polynomial_fst polynomial_first)
    (polynomial_pair (polynomial_snd polynomial_first) polynomial_second)

def clip (x : ℕ×ℕ) : ℕ := if x.2.size≤x.1 then x.2 else 0
def clipRealizer : Realizer clip :=
  (choose (composition (pair (composition second bitSize) first) leNat) second (constant 0)).congr (by
    intro x; simp only [clip,Function.comp_apply,decide_eq_true_eq])
omit [Codec A] [Codec B] in
lemma polynomial_clip : PolynomialTime clipRealizer := by
  unfold clipRealizer
  apply polynomial_congr
  apply polynomial_choose _ polynomial_second (polynomial_constant 0)
  apply polynomial_composition _ polynomial_leNat
  apply polynomial_pair (polynomial_composition polynomial_second polynomial_bitSize) polynomial_first
omit [Codec A] [Codec B] in
lemma clip_size (K n : ℕ) : (clip (K,n)).size≤K := by
  unfold clip
  split_ifs with h
  · exact h
  · simp
omit [Codec A] [Codec B] in
lemma clip_eq (K n : ℕ) (h : n.size≤K) : clip (K,n)=n := by simp [clip,h]
end MatchingFPRAS.TreeTyped

end OAI
