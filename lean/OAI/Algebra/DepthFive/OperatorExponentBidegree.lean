import OAI.Algebra.DepthFive.OperatorMonomials
import OAI.Algebra.DepthFive.OperatorRank

namespace OAI

/-! Degree and validity of the natural exponent produced by a mixed monomial operator. -/

noncomputable section

namespace Problem335

variable {σ : Type*}

/-- Filtering to derivative variables retains precisely the first bidegree. -/
theorem bidegreeWeight_derivExponent (isV : σ → Bool) (d : σ →₀ ℕ) :
    Finsupp.weight (bidegreeWeight isV) (derivExponent isV d) =
      ((Finsupp.weight (bidegreeWeight isV) d).1, 0) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp [derivExponent, Finsupp.filter_zero]; rfl
  | add d e hd he =>
    simp only [derivExponent, Finsupp.filter_add, map_add] at *
    rw [hd, he]
    rfl
  | single i r =>
    cases hi : isV i with
    | false =>
      simp [derivExponent, Finsupp.weight_single, bidegreeWeight, hi]
      rfl
    | true => simp [derivExponent, Finsupp.weight_single, bidegreeWeight, hi]

/-- Filtering to multiplication variables retains precisely the second bidegree. -/
theorem bidegreeWeight_mulExponent (isV : σ → Bool) (d : σ →₀ ℕ) :
    Finsupp.weight (bidegreeWeight isV) (mulExponent isV d) =
      (0, (Finsupp.weight (bidegreeWeight isV) d).2) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp [mulExponent, Finsupp.filter_zero]; rfl
  | add d e hd he =>
    simp only [mulExponent, Finsupp.filter_add, map_add] at *
    rw [hd, he]
    rfl
  | single i r =>
    cases hi : isV i with
    | false => simp [mulExponent, Finsupp.weight_single, bidegreeWeight, hi]
    | true =>
      simp [mulExponent, Finsupp.weight_single, bidegreeWeight, hi]
      rfl

/-- Availability of every derivative implies availability of the total derivative degree. -/
theorem bidegree_le_of_derivExponent_le (isV : σ → Bool) (d e : σ →₀ ℕ)
    {k m a b : ℕ} (hd : Finsupp.weight (bidegreeWeight isV) d = (k,m))
    (he : Finsupp.weight (bidegreeWeight isV) e = (a,b))
    (hle : derivExponent isV d ≤ e) : k ≤ a := by
  have hsplit := congrArg (Finsupp.weight (bidegreeWeight isV))
    (tsub_add_cancel_of_le hle)
  rw [map_add, bidegreeWeight_derivExponent, hd, he] at hsplit
  have hfst := congrArg Prod.fst hsplit
  dsimp at hfst
  omega

/-- A valid monomial action has a natural output exponent in exactly the required
finite bidegree fiber, without any coefficient-field assumptions. -/
theorem bidegreeWeight_operator_target (isV : σ → Bool) (d e : σ →₀ ℕ)
    {k m a b : ℕ} (hd : Finsupp.weight (bidegreeWeight isV) d = (k,m))
    (he : Finsupp.weight (bidegreeWeight isV) e = (a,b))
    (hle : derivExponent isV d ≤ e) :
    Finsupp.weight (bidegreeWeight isV)
      (e - derivExponent isV d + mulExponent isV d) = (a-k,b+m) := by
  have hsplit := congrArg (Finsupp.weight (bidegreeWeight isV))
    (tsub_add_cancel_of_le hle)
  rw [map_add, bidegreeWeight_derivExponent, hd, he] at hsplit
  have hf := congrArg Prod.fst hsplit
  have hs := congrArg Prod.snd hsplit
  rw [map_add, bidegreeWeight_mulExponent, hd]
  apply Prod.ext <;> dsimp at * <;> omega

end Problem335

end

end OAI
