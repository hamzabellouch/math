import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.PublicComposition
import OAI.Combinatorics.RamseyFive.Entropy.IndependentLaw
import OAI.Combinatorics.RamseyFive.Trees.PivotTree

namespace OAI

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical
universe u v w z
variable {A : Type u} {C : Type v} [Fintype C]
  (Ω : A→C→Type w) [∀a c,Fintype (Ω a c)]
  (p : ∀a c,Law (Ω a c))

lemma root_tape_law (a : A) (l r : BinaryTree A) (c : C) :
    map (tapeLaw Ω p (.node a l r)) (fun ω=>ω.1 c)=p a c := by
  exact (map_independent_left (piLaw (p a))
    (adaptiveLaw (tapeLaw Ω p l) (fun _=>tapeLaw Ω p r)) (fun ω=>ω c)).trans (piLaw_eval (p a) c)

lemma root_output_law {D : Type z} [Fintype D]
    (a : A) (l r : BinaryTree A) (c : C) (out : Ω a c→D) :
    map (tapeLaw Ω p (.node a l r)) (fun ω=>out (ω.1 c))=map (p a c) out := by
  have h := congrArg (fun q=>map q out) (root_tape_law Ω p a l r c)
  simpa only [map_comp,Function.comp_def] using h

lemma left_continuation_law {D : Type z} [Fintype D]
    (a : A) (l r : BinaryTree A) (c : C)
    (nextContext : Ω a c→Option C) (out : Option C→Tape Ω l→D) :
    map (tapeLaw Ω p (.node a l r)) (fun ω=>out (nextContext (ω.1 c)) ω.2.1)=
      map (adaptiveLaw (map (p a c) nextContext)
        (fun C=>map (tapeLaw Ω p l) (out C))) Prod.snd := by
  rw [tapeLaw]
  have h := public_composition (piLaw (p a))
    (adaptiveLaw (tapeLaw Ω p l) (fun _=>tapeLaw Ω p r))
    (fun ω=>nextContext (ω c)) (fun C ω=>out C ω.1)
    (fun C=>map (tapeLaw Ω p l) (out C))
    (fun C=>map_independent_left _ _ (out C))
  have hc : map (piLaw (p a)) (fun ω=>nextContext (ω c))=map (p a c) nextContext := by
    have ht := congrArg (fun q=>map q nextContext) (piLaw_eval (p a) c)
    simpa only [map_comp,Function.comp_def] using ht
  rw [hc] at h
  exact h

lemma right_continuation_law {D : Type z} [Fintype D]
    (a : A) (l r : BinaryTree A) (c : C)
    (nextContext : Ω a c→Option C) (out : Option C→Tape Ω r→D) :
    map (tapeLaw Ω p (.node a l r)) (fun ω=>out (nextContext (ω.1 c)) ω.2.2)=
      map (adaptiveLaw (map (p a c) nextContext)
        (fun C=>map (tapeLaw Ω p r) (out C))) Prod.snd := by
  rw [tapeLaw]
  have h := public_composition (piLaw (p a))
    (adaptiveLaw (tapeLaw Ω p l) (fun _=>tapeLaw Ω p r))
    (fun ω=>nextContext (ω c)) (fun C ω=>out C ω.2)
    (fun C=>map (tapeLaw Ω p r) (out C))
    (fun C=>map_independent_right _ _ (out C))
  have hc : map (piLaw (p a)) (fun ω=>nextContext (ω c))=map (p a c) nextContext := by
    have ht := congrArg (fun q=>map q nextContext) (piLaw_eval (p a) c)
    simpa only [map_comp,Function.comp_def] using ht
  rw [hc] at h
  exact h
end SharpRamseyFive.TreeCodec

end OAI
