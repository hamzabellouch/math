import Mathlib
import OAI.Probability.SKGap.Matrix.WordDiagUniform
import OAI.Probability.SKGap.Localization.LiteralSeriesLiftAppend

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open Diagram InverseDiagram WordSeries PowerSeries
variable {ι : Type*} [Fintype ι]

lemma polynomial_coe_list_sum (L : List (Polynomial ℝ)) :
    (L.sum : ℝ⟦X⟧)=(L.map (fun p : Polynomial ℝ=> (p : ℝ⟦X⟧))).sum :=
  map_list_sum Polynomial.coeToPowerSeries.ringHom L
lemma polynomial_coe_finset_sum {α : Type*} (S : Finset α) (f : α→Polynomial ℝ) :
    ((∑ k∈S,f k : Polynomial ℝ) : ℝ⟦X⟧)=∑ k∈S,(f k : ℝ⟦X⟧) :=
  map_sum Polynomial.coeToPowerSeries.ringHom f S

theorem literalSeries_eq_wordPredictionPolynomial (j : ℝ) (a : ι→ℝ)
    (F : List (WordLetter ι)) (hI : inverseCount F≤1) (i : ι) :
    literalSeries j a F i=(wordPredictionPolynomial j a F i : ℝ⟦X⟧) := by
  generalize hk : ordinaryCount F=k
  induction k using Nat.strong_induction_on generalizing F i with
  | h k ih =>
    by_cases ho : ordinaryCount F=0
    · rw [literalSeries_base j a F hI ho,wordPredictionPolynomial,ite_eq_left ho,Polynomial.coe_C]
    · have hsub (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
          (∀ u,literalSeries j a t.inner u=(wordPredictionPolynomial j a t.inner u : ℝ⟦X⟧)) ∧
          (∀ u,literalSeries j a t.outer u=(wordPredictionPolynomial j a t.outer u : ℝ⟦X⟧)) := by
        have hd := wordRecursionTerms_decreases a F t ht
        have hI' := wordRecursionTerms_one_inverse a F hI t ht
        exact ⟨fun u=>ih _ (by omega) _ hI'.2 u rfl,fun u=>ih _ (by omega) _ hI'.1 u rfl⟩
      have hrec : literalSeries j a F i=
          ((wordRecursionTerms a F).map (fun t=>
            (if t.inversePartner then X else 1)*C j*meanSeries (literalSeries j a t.inner)*
              literalSeries j a t.outer i)).sum := by
        cases hs : firstNoiseSplit F with
        | none => exact False.elim (ho ((firstNoiseSplit_none F).mp hs))
        | some pq =>
          rcases pq with ⟨P,Q⟩
          have he := firstNoiseSplit_some F P Q hs
          rw [wordRecursionTerms,hs]
          simpa only [he] using literalSeries_at j a P Q (by simpa only [he] using hI) i
      rw [hrec,wordPredictionPolynomial,ite_eq_right ho,polynomial_coe_list_sum,List.map_map]
      rw [← List.attach_map_val (l := wordRecursionTerms a F)]
      congr 1
      apply List.map_congr_left
      intro t ht
      have hs := hsub t.val t.property
      simp only [Function.comp_def,Polynomial.coe_mul,Polynomial.coe_C]
      have hm : meanSeries (literalSeries j a t.val.inner)=
          ((Polynomial.C ((Fintype.card ι:ℝ)⁻¹)*(∑ k,wordPredictionPolynomial j a t.val.inner k) : Polynomial ℝ) : ℝ⟦X⟧) := by
        simp only [meanSeries,Polynomial.coe_mul,Polynomial.coe_C,polynomial_coe_finset_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro u _
        exact hs.1 u
      rw [hs.2 i]
      rw [hm]
      cases t.val.inversePartner <;> simp only [Bool.false_eq_true,↓reduceIte,Polynomial.coe_one,Polynomial.coe_X,
        Polynomial.coe_mul,Polynomial.coe_C]

end SKGap.Noncrossing

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
