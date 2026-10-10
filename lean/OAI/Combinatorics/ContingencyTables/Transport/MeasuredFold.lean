import OAI.Combinatorics.MatchingCount.Complexity.TreeCostMeasure

namespace OAI

/-! # List folds with the cost of each cached computation accounted for -/

namespace ContingencyTables.MeasuredFold
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

variable {A B : Type} [Codec A] [Codec B]

/-- The loop cost is polynomial in one common external measure whenever
each reached call and each stored accumulator satisfy such a bound. -/
lemma work_fold {f : A×B → B} (F : Realizer f) (measure : List A×B → ℕ)
    (p q : Polynomial ℕ)
    (hinput : ∀ z,weight z ≤ measure z)
    (hcall : ∀ (as : List A) (b : B) pre a post,as=pre++a::post →
      F.cost (a,pre.foldl (fun z c => f (c,z)) b) ≤ p.eval (measure (as,b)))
    (hstate : ∀ (as : List A) (b : B) pre post,as=pre++post →
      weight (pre.foldl (fun z a => f (a,z)) b) ≤ q.eval (measure (as,b))) :
    WorkBound (fold F) measure := by
  refine ⟨X*(p+14*X+34)+10+q,?_⟩
  rintro ⟨as,b⟩
  let S := measure (as,b)
  have hs : weight as ≤ S := by
    have hi := hinput (as,b)
    rw [weight_prod] at hi
    exact le_trans (by omega : weight as≤1+weight as+weight b) hi
  have hc := Fold.cost_prefix_bound (f := f) F.cost as b (p.eval S) S hs
    (hcall as b)
  have hout := hstate as b as [] (by simp)
  have hlen : as.length ≤ S := (list_length_le_weight as).trans hs
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change Fold.cost f F.cost as b+weight (as.foldl (fun z a => f (a,z)) b) ≤ _
  change _ ≤ S*(p.eval S+14*S+34)+10+q.eval S
  have hm := Nat.mul_le_mul_right (p.eval S+14*S+34) hlen
  change _ ≤ q.eval S at hout
  omega

end ContingencyTables.MeasuredFold

end OAI
