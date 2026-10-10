import OAI.Analysis.KadisonSimilarity.Tensor.TensorDensity
import Mathlib.Logic.Equiv.Option
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-!
# Factorization of matrix contractions along pairs

This is the finite combinatorial bridge between the cycle expansion and the
bilinear pairing polynomials: each two-cycle contributes exactly one trace of
a product. The normalization uses the actual number of matching orbits.
-/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- Choose the lower-ranked vertex in each pair. -/
abbrev MatchingRepresentatives (rank : ι → ℕ) (P : PerfectMatching ι) :=
  {i : ι // rank i < rank (P.1 i)}

instance matchingRepresentativesFintype (rank : ι → ℕ) (P : PerfectMatching ι) :
    Fintype (MatchingRepresentatives rank P) := Fintype.ofFinite _

omit [Fintype ι] [DecidableEq ι] in
private theorem matching_rank_ne (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) (i : ι) : rank i ≠ rank (P.1 i) :=
  fun h => P.2.2 i (hrank h).symm

/-- The vertices split into a representative and its partner, once per pair. -/
def matchingSplitEquiv (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) :
    MatchingRepresentatives rank P ⊕ MatchingRepresentatives rank P ≃ ι :=
  Equiv.ofBijective (Sum.elim Subtype.val (fun i => P.1 i)) (by
    constructor
    · intro a b hab
      cases a with
      | inl i =>
        cases b with
        | inl j => exact congrArg Sum.inl (Subtype.ext hab)
        | inr j =>
          have hi := i.property
          have hj := j.property
          change i.val = P.1 j.val at hab
          rw [hab, P.2.1] at hi
          omega
      | inr i =>
        cases b with
        | inl j =>
          have hi := i.property
          have hj := j.property
          change P.1 i.val = j.val at hab
          rw [← hab, P.2.1] at hj
          omega
        | inr j => exact congrArg Sum.inr (Subtype.ext (P.1.injective hab))
    · intro i
      by_cases hi : rank i < rank (P.1 i)
      · exact ⟨Sum.inl ⟨i, hi⟩, rfl⟩
      · have hne := matching_rank_ne rank hrank P i
        have hpi : rank (P.1 i) < rank (P.1 (P.1 i)) := by rw [P.2.1]; omega
        exact ⟨Sum.inr ⟨P.1 i, hpi⟩, P.2.1 i⟩)

omit [Fintype ι] in
@[simp] theorem matchingSplitEquiv_inl (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) (i : MatchingRepresentatives rank P) :
    matchingSplitEquiv rank hrank P (Sum.inl i) = i := rfl

omit [Fintype ι] in
@[simp] theorem matchingSplitEquiv_inr (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) (i : MatchingRepresentatives rank P) :
    matchingSplitEquiv rank hrank P (Sum.inr i) = P.1 i := rfl

/-- Each matching orbit has exactly one lower-ranked representative. -/
def matchingClassEquiv (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) : MatchingRepresentatives rank P ≃ PermutationCycles P.1 :=
  Equiv.ofBijective (fun i => (⟦i.val⟧ : PermutationCycles P.1)) (by
    constructor
    · intro i j hij
      have hcycle := Quotient.exact hij
      rcases (sameCycle_perfectMatching_iff P i.val j.val).mp hcycle with h | h
      · exact Subtype.ext h.symm
      · have hi := i.property
        have hj := j.property
        rw [h, P.2.1] at hj
        omega
    · intro q
      induction q using Quotient.inductionOn with
      | h i =>
        by_cases hi : rank i < rank (P.1 i)
        · exact ⟨⟨i, hi⟩, rfl⟩
        · have hne := matching_rank_ne rank hrank P i
          have hpi : rank (P.1 i) < rank (P.1 (P.1 i)) := by rw [P.2.1]; omega
          refine ⟨⟨P.1 i, hpi⟩, Quotient.sound ?_⟩
          exact (sameCycle_perfectMatching_iff P (P.1 i) i).mpr (Or.inr (P.2.1 i).symm))

theorem permutationCycleCount_matching (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) :
    permutationCycleCount P.1 = Fintype.card (MatchingRepresentatives rank P) := by
  rw [permutationCycleCount, Nat.card_eq_fintype_card]
  exact (Fintype.card_congr (matchingClassEquiv rank hrank P)).symm

/-- The unnormalized coordinate contraction of a matching is a product of
ordinary matrix traces, one for each pair. -/
theorem permutationContraction_matching (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) (v : ι → Matrix α α ℂ) :
    permutationContraction P.1 v =
      ∏ i : MatchingRepresentatives rank P, Matrix.trace (v i * v (P.1 i)) := by
  classical
  let R := MatchingRepresentatives rank P
  let e := matchingSplitEquiv rank hrank P
  let d : (ι → α) ≃ (R → α) × (R → α) :=
    (Equiv.arrowCongr e.symm (Equiv.refl α)).trans (Equiv.sumArrowEquivProdArrow R R α)
  unfold permutationContraction
  rw [Fintype.sum_equiv d _ (fun fg =>
    ∏ i : R, v i (fg.1 i) (fg.2 i) * v (P.1 i) (fg.2 i) (fg.1 i))]
  · rw [Fintype.sum_prod_type]
    have hinner (f : R → α) :
        (∑ g : R → α, ∏ i : R, v i.val (f i) (g i) * v (P.1 i.val) (g i) (f i)) =
          ∏ i : R, ∑ b : α, v i.val (f i) b * v (P.1 i.val) b (f i) :=
      (Fintype.prod_sum (fun (i : R) (b : α) =>
        v i.val (f i) b * v (P.1 i.val) b (f i))).symm
    simp_rw [hinner]
    rw [← Fintype.prod_sum (fun (i : R) (a : α) =>
      ∑ b : α, v i.val a b * v (P.1 i.val) b a)]
    apply Finset.prod_congr rfl
    intro i _
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  · intro f
    change (∏ i, v i (f i) (f (P.1 i))) =
      ∏ i : R, v i (f i) (f (P.1 i)) * v (P.1 i) (f (P.1 i)) (f i)
    rw [← e.prod_comp (fun i => v i (f i) (f (P.1 i))), Fintype.prod_sum_type]
    simp only [e, matchingSplitEquiv_inl, matchingSplitEquiv_inr]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [P.2.1]

/-- The normalized contraction uses one normalized trace for each pair. -/
theorem normalizedPermutationContraction_matching
    (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) (v : ι → Matrix α α ℂ) :
    normalizedPermutationContraction P.1 v =
      ∏ i : MatchingRepresentatives rank P,
        (Fintype.card α : ℂ)⁻¹ * Matrix.trace (v i * v (P.1 i)) := by
  rw [normalizedPermutationContraction, permutationCycleCount_matching rank hrank P,
    permutationContraction_matching rank hrank P, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]

omit [DecidableEq ι] in
/-- The orbit of an involution consists of the point and its partner, allowing
also the fixed-point case used for the endpoint. -/
theorem sameCycle_involutive_iff (π : Equiv.Perm ι) (hπ : Function.Involutive π)
    (i j : ι) : π.SameCycle i j ↔ j = i ∨ j = π i := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with h | h
      · exact Or.inr (congrArg π h)
      · exact Or.inl ((congrArg π h).trans (hπ i))
  · rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.rfl
    · exact ⟨1, by simp⟩

/-- Add a fixed distinguished endpoint to a tail matching. -/
def endpointMatching (P : PerfectMatching ι) : Equiv.Perm (Option ι) :=
  P.1.optionCongr

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem endpointMatching_none (P : PerfectMatching ι) :
    endpointMatching P none = none := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem endpointMatching_some (P : PerfectMatching ι) (i : ι) :
    endpointMatching P (some i) = some (P.1 i) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem endpointMatching_involutive (P : PerfectMatching ι) :
    Function.Involutive (endpointMatching P) := by
  intro i
  cases i with
  | none => rfl
  | some i => exact congrArg some (P.2.1 i)

omit [Fintype ι] [DecidableEq ι] in
theorem endpointMatching_isEndpointPairing (P : PerfectMatching ι) :
    EndpointPairing (endpointMatching P) none := by
  refine ⟨rfl, endpointMatching_involutive P, ?_⟩
  intro i hi
  cases i with
  | none => rfl
  | some i => exact False.elim (P.2.2 i (Option.some.inj hi))

/-- The endpoint supplies one additional singleton orbit. -/
def endpointMatchingClassEquiv (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) :
    Option (MatchingRepresentatives rank P) ≃ PermutationCycles (endpointMatching P) :=
  Equiv.ofBijective (fun i => (⟦Option.map Subtype.val i⟧ :
    PermutationCycles (endpointMatching P))) (by
    constructor
    · intro i j hij
      let u : Option (MatchingRepresentatives rank P) → Option ι := Option.map Subtype.val
      change (⟦u i⟧ : PermutationCycles (endpointMatching P)) = ⟦u j⟧ at hij
      have hc := (sameCycle_involutive_iff (endpointMatching P)
        (endpointMatching_involutive P) (u i) (u j)).mp (Quotient.exact hij)
      cases i with
      | none =>
        cases j with
        | none => rfl
        | some j => rcases hc with h | h <;> cases h
      | some i =>
        cases j with
        | none => rcases hc with h | h <;> cases h
        | some j =>
          rcases hc with h | h
          · exact congrArg some (Subtype.ext (Option.some.inj h).symm)
          · have heq : j.val = P.1 i.val := Option.some.inj h
            have hi := i.property
            have hj := j.property
            rw [heq, P.2.1] at hj
            omega
    · intro q
      induction q using Quotient.inductionOn with
      | h i =>
        cases i with
        | none => exact ⟨none, rfl⟩
        | some i =>
          by_cases hi : rank i < rank (P.1 i)
          · exact ⟨some ⟨i, hi⟩, rfl⟩
          · have hne := matching_rank_ne rank hrank P i
            have hpi : rank (P.1 i) < rank (P.1 (P.1 i)) := by rw [P.2.1]; omega
            refine ⟨some ⟨P.1 i, hpi⟩, Quotient.sound ?_⟩
            apply (sameCycle_involutive_iff (endpointMatching P)
              (endpointMatching_involutive P) _ _).mpr
            exact Or.inr (congrArg some (P.2.1 i).symm))

theorem permutationCycleCount_endpointMatching (rank : ι → ℕ)
    (hrank : Function.Injective rank) (P : PerfectMatching ι) :
    permutationCycleCount (endpointMatching P) =
      Fintype.card (MatchingRepresentatives rank P) + 1 := by
  rw [permutationCycleCount, Nat.card_eq_fintype_card,
    ← Fintype.card_congr (endpointMatchingClassEquiv rank hrank P), Fintype.card_option]

/-- Splitting the endpoint coordinate leaves precisely the tail contraction. -/
theorem permutationContraction_endpointMatching (P : PerfectMatching ι)
    (v : Option ι → Matrix α α ℂ) :
    permutationContraction (endpointMatching P) v =
      Matrix.trace (v none) * permutationContraction P.1 (fun i => v (some i)) := by
  classical
  unfold permutationContraction
  rw [Fintype.sum_equiv (Equiv.piOptionEquivProd (β := fun _ : Option ι => α)) _
    (fun fg => v none fg.1 fg.1 * ∏ i, v (some i) (fg.2 i) (fg.2 (P.1 i)))]
  · rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    rfl
  · intro f
    rw [Fintype.prod_option]
    rfl

/-- Each surviving finite-stage cycle form is the endpoint trace times the
product of normalized pair traces. -/
theorem normalizedPermutationContraction_endpointMatching
    (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) (v : Option ι → Matrix α α ℂ) :
    normalizedPermutationContraction (endpointMatching P) v =
      ((Fintype.card α : ℂ)⁻¹ * Matrix.trace (v none)) *
        ∏ i : MatchingRepresentatives rank P,
          (Fintype.card α : ℂ)⁻¹ * Matrix.trace (v (some i) * v (some (P.1 i))) := by
  rw [normalizedPermutationContraction, permutationCycleCount_endpointMatching rank hrank P,
    pow_succ, permutationContraction_endpointMatching,
    permutationContraction_matching rank hrank P, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  ring

omit [Fintype ι] [DecidableEq ι] in
private theorem optionPerm_some (π : Equiv.Perm (Option ι)) (hnone : π none = none)
    (i : ι) : ∃ j, π (some i) = some j := by
  cases h : π (some i) with
  | none => exact False.elim (Option.some_ne_none i (π.injective (h.trans hnone.symm)))
  | some j => exact ⟨j, rfl⟩

/-- Remove the distinguished fixed endpoint from a surviving permutation. -/
def endpointTailMatching (π : Equiv.Perm (Option ι)) (hπ : EndpointPairing π none) :
    PerfectMatching ι :=
  ⟨π.removeNone, by
    have hs (i : ι) : some (π.removeNone i) = π (some i) :=
      π.removeNone_some (optionPerm_some π hπ.1 i)
    constructor
    · intro i
      apply Option.some.inj
      calc
        some (π.removeNone (π.removeNone i)) = π (some (π.removeNone i)) := hs _
        _ = π (π (some i)) := congrArg π (hs i)
        _ = some i := hπ.2.1 _
    · intro i hi
      have hfix : π (some i) = some i := (hs i).symm.trans (congrArg some hi)
      exact Option.some_ne_none i (hπ.2.2 (some i) hfix)⟩

omit [Fintype ι] [DecidableEq ι] in
theorem endpointMatching_tail (π : Equiv.Perm (Option ι)) (hπ : EndpointPairing π none) :
    endpointMatching (endpointTailMatching π hπ) = π := by
  apply Equiv.ext
  intro i
  cases i with
  | none => exact hπ.1.symm
  | some i => exact π.removeNone_some (optionPerm_some π hπ.1 i)

/-- Surviving permutations are in bijection with tail matchings. -/
def endpointMatchingEquiv : PerfectMatching ι ≃
    {π : Equiv.Perm (Option ι) // EndpointPairing π none} :=
  Equiv.ofBijective (fun P => ⟨endpointMatching P, endpointMatching_isEndpointPairing P⟩) (by
    constructor
    · intro P Q heq
      apply Subtype.ext
      apply Equiv.ext
      intro i
      exact Option.some.inj (congrArg (fun π => π.val (some i)) heq)
    · intro π
      exact ⟨endpointTailMatching π.val π.property, Subtype.ext (endpointMatching_tail _ _)⟩)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem endpointMatchingEquiv_apply (P : PerfectMatching ι) :
    (endpointMatchingEquiv P).val = endpointMatching P := rfl

/-- Combining the cycle threshold, centered singleton deletion, and explicit
matrix factorization yields exactly the finite-stage pairing expansion. -/
theorem invariant_expansion_tail_pairings
    (rank : ι → ℕ) (hrank : Function.Injective rank)
    (v : Option ι → Matrix α α ℂ) (hcenter : ∀ i, Matrix.trace (v (some i)) = 0)
    (c : Equiv.Perm (Option ι) → ℂ)
    (hsmall : ∀ π, 2 * permutationCycleCount π < Fintype.card (Option ι) + 1 → c π = 0) :
    (∑ π, c π * normalizedPermutationContraction π v) =
      ((Fintype.card α : ℂ)⁻¹ * Matrix.trace (v none)) *
        ∑ P : PerfectMatching ι, c (endpointMatching P) *
          ∏ i : MatchingRepresentatives rank P,
            (Fintype.card α : ℂ)⁻¹ * Matrix.trace (v (some i) * v (some (P.1 i))) := by
  classical
  rw [invariant_expansion_reduce_to_pairings none v (by
    intro i hi
    cases i with
    | none => exact False.elim (hi rfl)
    | some i => exact hcenter i) c hsmall]
  rw [Finset.sum_subtype (p := fun π : Equiv.Perm (Option ι) => EndpointPairing π none)
    (Finset.univ.filter (fun π => EndpointPairing π none)) (by simp)
    (fun π => c π * normalizedPermutationContraction π v)]
  rw [← endpointMatchingEquiv.sum_comp]
  simp only [endpointMatchingEquiv_apply,
    normalizedPermutationContraction_endpointMatching rank hrank]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P _
  ring

section HilbertStage

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- In a tracial Hilbert-stage realization, the matrix factorization is the
same continuous bilinear pairing polynomial used after taking density. -/
theorem normalizedPermutationContraction_endpointMatching_eq_pairingPolynomial
    (rank : ι → ℕ) (hrank : Function.Injective rank)
    (P : PerfectMatching ι) (v : Option ι → Matrix α α ℂ)
    (embed : Matrix α α ℂ → E) (B : E →L[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ a b, B (embed a) (embed b) =
      (Fintype.card α : ℂ)⁻¹ * Matrix.trace (a * b)) :
    normalizedPermutationContraction (endpointMatching P) v =
      ((Fintype.card α : ℂ)⁻¹ * Matrix.trace (v none)) *
        pairingPolynomial rank B P (fun i => embed (v (some i))) := by
  classical
  rw [normalizedPermutationContraction_endpointMatching rank hrank P]
  congr 1
  unfold pairingPolynomial
  simp only [hB]
  symm
  exact Finset.prod_subtype
    (Finset.univ.filter (fun i => rank i < rank (P.1 i))) (by simp)
    (fun i => (Fintype.card α : ℂ)⁻¹ * Matrix.trace (v (some i) * v (some (P.1 i))))

end HilbertStage

end KadisonSimilarity

end

end OAI
