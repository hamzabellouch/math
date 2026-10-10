import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineLadderSchedule
import OAI.Combinatorics.MatchingCount.Complexity.OnlineRequestCost

namespace OAI

namespace MatchingFPRAS.TreeTyped
open NumericBounds

variable {A B C : Type} [Codec A] [Codec B] [Codec C]
lemma work_comp_bound {f : A→B} {g : B→C} {F : Realizer f} {G : Realizer g}
    {m : A→ℕ} {n : B→ℕ} (hF : WorkBound F m) (hG : WorkBound G n)
    (h : Bound (n ∘ f) m) : WorkBound (composition F G) m := by
  obtain ⟨p,hp⟩:=h
  exact work_composition hF hG p hp
lemma work_lift_bound {f : A→B} {F : Realizer f} {m : A→ℕ}
    (hF : PolynomialTime F) (h : Bound weight m) : WorkBound F m := by
  obtain ⟨p,hp⟩:=h
  exact work_of_polynomial hF p hp
lemma work_remeasure_bound {f : A→B} {F : Realizer f} {m n : A→ℕ}
    (hF : WorkBound F m) (h : Bound m n) : WorkBound F n := by
  obtain ⟨p,hp⟩:=h
  exact work_remeasure hF p hp
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial NumericBounds ExecutableSource Transport

def vertexMeasure (x : ℕ×ℕ) : ℕ := x.1+x.2+TreeTyped.weight x
lemma work_vertexNumber : WorkBound vertexNumberRealizer vertexMeasure := by
  have lift {A : Type} [Codec A] {f : (ℕ×ℕ)→A} {F : Realizer f} (hF : PolynomialTime F) :
      WorkBound F vertexMeasure := work_of_polynomial hF X (fun x=>by simp [vertexMeasure])
  unfold vertexNumberRealizer
  apply work_then_polynomial _ polynomial_listLength
  apply work_then_polynomial _ polynomial_vertices
  apply work_pair _ _ X (fun x=>by simp [vertexMeasure])
  · exact work_composition (lift polynomial_first) range_numeric_work X (by
      intro x;simp only [Polynomial.eval_X,id_eq];unfold vertexMeasure;omega)
  · apply work_fuelAfter (lift (polynomial_addNat
      (polynomial_mulNat (polynomial_constant _) polynomial_second) (polynomial_constant _))) (2*X+2)
    intro x
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    change 2*x.2+2 ≤ 2*vertexMeasure x+2
    unfold vertexMeasure;omega

def ladderMeasure (x : LadderInput) : ℕ := x.1.1+x.1.2+x.2+TreeTyped.weight x
lemma work_ladderSearchInput : WorkBound ladderSearchInputRealizer ladderMeasure := by
  have lift {A : Type} [Codec A] {f : LadderInput→A} {F : Realizer f} (hF : PolynomialTime F) :
      WorkBound F ladderMeasure := work_of_polynomial hF X (fun x=>by simp [ladderMeasure])
  unfold ladderSearchInputRealizer
  apply work_pair _ _ X (fun x=>by simp [ladderMeasure])
  · apply work_then_polynomial _ polynomial_ladderPowerPlan
    apply work_pair (lift polynomial_first) _ X (fun x=>by simp [ladderMeasure])
    apply work_fuelAfter (lift polynomial_second) X
    intro x;simp only [Polynomial.eval_X];unfold ladderMeasure;omega
  · apply work_fuelAfter (lift polynomial_tierBound) (X^2*(X+2*X+2))
    intro x
    have hn : x.1.1 ≤ ladderMeasure x := by unfold ladderMeasure;omega
    have hd : x.1.2 ≤ ladderMeasure x := by unfold ladderMeasure;omega
    have hk : x.2 ≤ ladderMeasure x := by unfold ladderMeasure;omega
    have hb:=NumericBounds.clog_le x.1.2
    simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
    change tierBound x.1.1 x.1.2 x.2 ≤ _
    unfold tierBound
    gcongr; omega
lemma work_ladderSchedule : WorkBound ladderScheduleRealizer ladderMeasure :=
  work_then_polynomial work_ladderSearchInput polynomial_findPower
end MatchingFPRAS.OnlineSchedule

end OAI
