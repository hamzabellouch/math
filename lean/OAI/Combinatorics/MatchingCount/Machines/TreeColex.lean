import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeFiniteOps

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B : Type} [Codec A] [Codec B] [LinearOrder A] [LinearOrder B]

def boolOr : Realizer (fun x : Bool×Bool=>x.1 || x.2) :=
  (choose first (constant true) second).congr (by intro x; cases x.1 <;> rfl)
lemma polynomial_boolOr : PolynomialTime boolOr := by
  unfold boolOr
  exact polynomial_congr _ (polynomial_choose polynomial_first (polynomial_constant true) polynomial_second)

def colexLe (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) :
    Realizer (fun x : Finset A×Finset A=>decide (toColex x.1≤toColex x.2)) :=
  (composition (pair (composition (pair second first) (finsetSDiff E)) (finsetSDiff E))
    (finsetAll (composition (pair second first) (finsetAny R)))).congr (by
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply,decide_eq_true_eq,Finset.mem_sdiff]
      rw [Finset.Colex.toColex_le_toColex]
      constructor
      · intro h a ha hn
        obtain ⟨b,⟨hb,hbn⟩,hab⟩:=h a ⟨ha,hn⟩
        exact ⟨b,hb,hbn,hab⟩
      · intro h a ⟨ha,hn⟩
        obtain ⟨b,hb,hbn,hab⟩:=h ha hn
        exact ⟨b,⟨hb,hbn⟩,hab⟩)
lemma polynomial_colexLe {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (colexLe E R) := by
  unfold colexLe
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) (polynomial_finsetSDiff hE))
    (polynomial_finsetSDiff hE))
    (polynomial_finsetAll (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_finsetAny hR)))

def lexLe (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2)))
    (S : Realizer (fun x : B×B=>decide (x.1≤x.2))) :
    Realizer (fun x : (A×B)×(A×B)=>decide (toLex x.1≤toLex x.2)) :=
  (composition (pair (composition (pair first.fst second.fst) R)
    (composition (pair (composition (composition (pair first.fst second.fst) E) boolNot)
      (composition (pair first.snd second.snd) S)) boolOr)) boolAnd).congr (by
        intro x
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',
          decide_eq_true_eq,decide_eq_false_iff_not,Prod.Lex.le_iff]
        rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
        dsimp only
        constructor
        · rintro ⟨h,h'⟩
          rcases lt_or_eq_of_le h with h | h
          · exact Or.inl h
          · exact Or.inr ⟨h,h'.resolve_left (not_not.mpr h)⟩
        · rintro (h|⟨h,h'⟩)
          · exact ⟨h.le,Or.inl (ne_of_lt h)⟩
          · exact ⟨h.le,Or.inr h'⟩)
lemma polynomial_lexLe {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    {S : Realizer (fun x : B×B=>decide (x.1≤x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) (hS : PolynomialTime S) :
    PolynomialTime (lexLe E R S) := by
  unfold lexLe
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_first) (polynomial_fst polynomial_second)) hR)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition
        (polynomial_pair (polynomial_fst polynomial_first) (polynomial_fst polynomial_second)) hE) polynomial_boolNot)
      (polynomial_composition (polynomial_pair (polynomial_snd polynomial_first) (polynomial_snd polynomial_second)) hS)) polynomial_boolOr))
    polynomial_boolAnd)
end MatchingFPRAS.TreeTyped

end OAI
