import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeExpectation
import Mathlib.Data.List.Induction

namespace OAI

/-! Under a tracial functional, vanishing of nonempty even alternating
centered words implies scalar freeness. The odd-word step rotates the last
letter next to the first, centers their product, and shortens the word. -/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
  {τ : R →ₗ[ℂ] ℂ} {P Q : StarSubalgebra ℂ R}

namespace AlternatingCenteredWord

/-- Any prefix retains the starting side and centered alternation. -/
theorem take_prefix {side : Bool} {xs ys : List R}
    (h : AlternatingCenteredWord τ P Q side (xs ++ ys)) :
    AlternatingCenteredWord τ P Q side xs := by
  induction xs generalizing side with
  | nil => exact .nil side
  | cons x xs ih =>
    cases h with
    | cons hm hz ht => exact .cons hm hz (ih ht)

/-- After an even prefix, the last letter lies in the starting algebra. -/
theorem last_mem_of_even_prefix {side : Bool} (xs : List R) (z : R)
    (h : AlternatingCenteredWord τ P Q side (xs ++ [z]))
    (heven : xs.length % 2 = 0) : z ∈ (if side then P else Q) := by
  induction xs using List.twoStepInduction generalizing side with
  | nil =>
    cases h with
    | cons hm _ _ => exact hm
  | singleton x => simp at heven
  | cons_cons x y xs ih _ =>
    cases h with
    | cons _ _ ht =>
      cases ht with
      | cons _ _ ht =>
        apply ih (side := side)
        · simpa only [Bool.not_not, List.append_eq] using ht
        · simp only [List.length_cons] at heven
          omega

/-- Appending the opposite-algebra letter closes an odd alternating word. -/
theorem append_of_odd_length {side : Bool} (xs : List R) (z : R)
    (h : AlternatingCenteredWord τ P Q side xs)
    (hodd : xs.length % 2 = 1) (hz : z ∈ (if !side then P else Q))
    (hz0 : τ z = 0) :
    AlternatingCenteredWord τ P Q side (xs ++ [z]) := by
  induction xs using List.twoStepInduction generalizing side with
  | nil => simp at hodd
  | singleton x =>
    cases h with
    | cons hm h0 _ =>
      exact .cons hm h0 (.cons hz hz0 (.nil _))
  | cons_cons x y xs ih _ =>
    cases h with
    | cons hm h0 ht =>
      cases ht with
      | cons hm' h0' ht' =>
        have htail : AlternatingCenteredWord τ P Q side xs := by
          simpa only [Bool.not_not] using ht'
        have hp : xs.length % 2 = 1 := by
          simp only [List.length_cons] at hodd
          omega
        exact .cons hm h0 (.cons hm' h0' (by
          simpa only [Bool.not_not, List.append_eq] using ih htail hp hz))

end AlternatingCenteredWord

/-- The tracial cyclic reduction needed in the dihedral-corner argument.
The only trace identities used are linearity, normalization, and cyclicity. -/
theorem scalarFree_of_even_alternating
    (hτ : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (heven : ∀ side x xs, AlternatingCenteredWord τ P Q side (x :: xs) →
      (x :: xs).length % 2 = 0 → τ ((x :: xs).prod) = 0) :
    ScalarFree τ P Q := by
  have hall : ∀ w : List R, ∀ side, w ≠ [] →
      AlternatingCenteredWord τ P Q side w → τ w.prod = 0 := by
    intro w
    induction w using List.bidirectionalRec with
    | nil => intro _ hne; exact (hne rfl).elim
    | singleton a =>
      intro side _ hw
      cases hw with
      | cons _ hz _ => simpa using hz
    | cons_append a xs b ih =>
      intro side _ hw
      by_cases hp : (a :: (xs ++ [b])).length % 2 = 0
      · exact heven side a (xs ++ [b]) hw hp
      have hlength : (a :: xs).length % 2 = 0 := by
        simp only [List.length_cons, List.length_append, List.length_nil] at hp ⊢
        omega
      have hb : b ∈ (if side then P else Q) :=
        AlternatingCenteredWord.last_mem_of_even_prefix (a :: xs) b hw hlength
      cases hw with
      | cons ha _ ht =>
        have hmid : AlternatingCenteredWord τ P Q (!side) xs := ht.take_prefix
        have hne : xs ≠ [] := by
          intro hx
          subst xs
          simp at hp
        have hshort : τ xs.prod = 0 := ih (!side) hne hmid
        have hc : traceCentered τ (b * a) ∈ (if side then P else Q) :=
          traceCentered_mem τ _ ((if side then P else Q).mul_mem hb ha)
        have hcenter : τ (traceCentered τ (b * a) * xs.prod) = 0 := by
          have hword : AlternatingCenteredWord τ P Q side
              (traceCentered τ (b * a) :: xs) :=
            .cons hc (traceCentered_trace τ hτ _) hmid
          simpa only [List.prod_cons] using heven side _ xs hword hlength
        calc
          τ ((a :: (xs ++ [b])).prod) = τ ((a * xs.prod) * b) := by
            simp only [List.prod_cons, List.prod_append, List.prod_nil, mul_one, mul_assoc]
          _ = τ (b * (a * xs.prod)) := htr _ _
          _ = τ ((b * a) * xs.prod) := by rw [mul_assoc]
          _ = τ ((traceCentered τ (b * a) + τ (b * a) • 1) * xs.prod) := by
            rw [traceCentered_add]
          _ = 0 := by
            rw [add_mul, smul_mul_assoc, one_mul, map_add, map_smul,
              hcenter, hshort]
            simp
  intro side x xs hw
  exact hall (x :: xs) side (List.cons_ne_nil _ _) hw

/-- It suffices to test even cyclic words beginning in the first algebra;
tracial rotation supplies the opposite starting side. -/
theorem scalarFree_of_even_cyclic
    (hτ : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (heven : ∀ x xs, AlternatingCenteredWord τ P Q true (x :: xs) →
      (x :: xs).length % 2 = 0 → τ ((x :: xs).prod) = 0) :
    ScalarFree τ P Q := by
  apply scalarFree_of_even_alternating hτ htr
  intro side x xs hw hp
  cases side with
  | true => exact heven x xs hw hp
  | false =>
    cases hw with
    | cons hx hx0 ht =>
      have hodd : xs.length % 2 = 1 := by
        simp only [List.length_cons] at hp
        omega
      have hrot : AlternatingCenteredWord τ P Q true (xs ++ [x]) :=
        ht.append_of_odd_length xs x hodd hx hx0
      have hne : xs ≠ [] := by
        intro h
        simp [h] at hodd
      obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
      have hv : τ ((y :: (ys ++ [x])).prod) = 0 := by
        apply heven y (ys ++ [x]) hrot
        simp only [List.length_cons, List.length_append, List.length_nil] at hp ⊢
        omega
      calc
        τ ((x :: y :: ys).prod) = τ ((y :: ys).prod * x) := by
          simp only [List.prod_cons]
          exact htr _ _
        _ = 0 := by
          simpa only [List.prod_cons, List.prod_append, List.prod_nil, mul_one,
            mul_assoc] using hv

end KadisonSimilarity

end

end OAI
