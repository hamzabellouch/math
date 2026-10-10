import OAI.Algebra.DepthFive.BidegreeAverages
import OAI.Algebra.DepthFive.FirstOccupationMoment

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.BidegreeAverages

/-- The function representation of a weak composition and the finite
`finsuppAntidiag` representation used by occupation moments agree coordinatewise. -/
def compositionAntidiagEquiv (σ : Type*) [Fintype σ] [DecidableEq σ] (a : ℕ) :
    Composition σ a ≃ (Finset.finsuppAntidiag (Finset.univ : Finset σ) a) := by
  refine Finsupp.equivFunOnFinite.symm.subtypeEquiv ?_
  intro d
  simp only [Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
  rfl

@[simp] theorem compositionAntidiagEquiv_apply (σ : Type*)
    [Fintype σ] [DecidableEq σ] (a : ℕ) (d : Composition σ a) (i : σ) :
    (compositionAntidiagEquiv σ a d).val i = d.val i := rfl

/-- Convert a sum over function compositions to the canonical occupation finset. -/
theorem sum_compositions_eq_antidiag {σ : Type*} [Fintype σ] [DecidableEq σ]
    (a : ℕ) (f : (σ → ℕ) → ℝ) :
    (∑' d : Composition σ a, f d.val) =
      ∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset σ) a, f M := by
  calc
    _ = ∑' M : (Finset.finsuppAntidiag (Finset.univ : Finset σ) a), f M.val :=
      (compositionAntidiagEquiv σ a).tsum_eq (fun M => f M.val)
    _ = _ := by
      rw [tsum_fintype]
      exact Finset.sum_coe_sort _ (fun M : σ →₀ ℕ => f M)

/-- Denominator conversion for the same index equivalence. -/
theorem card_compositions_eq_antidiag {σ : Type*} [Fintype σ] [DecidableEq σ]
    (a : ℕ) :
    Nat.card (Composition σ a) =
      (Finset.finsuppAntidiag (Finset.univ : Finset σ) a).card := by
  rw [Nat.card_congr (compositionAntidiagEquiv σ a), Nat.card_eq_fintype_card,
    Fintype.card_coe]

/-- The function-composition average is exactly the canonical occupation average. -/
theorem composition_average_eq_occupationAverage {σ : Type*}
    [Fintype σ] [DecidableEq σ] (a : ℕ) (f : (σ → ℕ) → ℝ) :
    (∑' d : Composition σ a, f d.val) / (Nat.card (Composition σ a) : ℝ) =
      occupationAverage a (fun M : σ →₀ ℕ => f M) := by
  rw [sum_compositions_eq_antidiag, card_compositions_eq_antidiag]
  rfl

/-- The actual bidegree-domain average, expressed directly using the canonical
occupation-average API. This bridges the Fock/matrix source indices and both
first- and second-moment inequalities. -/
theorem bidegree_average_eq_occupationAverage {σ : Type*} [Fintype σ] [DecidableEq σ]
    (isV : σ → Bool) (a b : ℕ)
    (f : ({x // isV x = true} → ℕ) → ℝ)
    (g : ({x // ¬ isV x = true} → ℕ) → ℝ) :
    (∑' d : Index isV a b,
      f (fun x => d.val x) * g (fun x => d.val x)) /
      (Nat.card (Index isV a b) : ℝ) =
      occupationAverage a (fun M : {x // isV x = true} →₀ ℕ => f M) *
        occupationAverage b (fun M : {x // ¬ isV x = true} →₀ ℕ => g M) := by
  classical
  rw [average_split, composition_average_eq_occupationAverage,
    composition_average_eq_occupationAverage]

/-- Matrix-indexed finite-sum version of the bridge. -/
theorem bidegree_average_eq_occupationAverage_fintype {σ : Type*}
    [Fintype σ] [DecidableEq σ] (isV : σ → Bool) (a b : ℕ)
    [Fintype (Index isV a b)]
    (f : ({x // isV x = true} → ℕ) → ℝ)
    (g : ({x // ¬ isV x = true} → ℕ) → ℝ) :
    (∑ d : Index isV a b,
      f (fun x => d.val x) * g (fun x => d.val x)) /
      (Fintype.card (Index isV a b) : ℝ) =
      occupationAverage a (fun M : {x // isV x = true} →₀ ℕ => f M) *
        occupationAverage b (fun M : {x // ¬ isV x = true} →₀ ℕ => g M) := by
  simpa only [tsum_fintype, Nat.card_eq_fintype_card] using
    bidegree_average_eq_occupationAverage isV a b f g

/-- The first occupation-moment lower estimate on the ACTUAL bidegree exponent
source, rather than on an auxiliary Cartesian product of composition finsets. -/
theorem bidegree_first_moment_lower {σ : Type*} [Fintype σ] [DecidableEq σ]
    (isV : σ → Bool) (a b : ℕ)
    [Fintype (Index isV a b)]
    [Nonempty {x // isV x = true}] [Nonempty {x // ¬ isV x = true}]
    (s : Finset {x // isV x = true}) (z : Finset {x // ¬ isV x = true})
    (ha : 0 < a) (hb : 0 < b) (hs : 2 * s.card ≤ a) (hz : 2 * z.card ≤ b) :
    Real.exp ((-(s.card : ℝ) ^ 2 / a -
        (s.card : ℝ) ^ 2 / (2 * Fintype.card {x // isV x = true})) +
      (-(z.card : ℝ) ^ 2 / b -
        (z.card : ℝ) ^ 2 / (2 * Fintype.card {x // ¬ isV x = true}))) *
      (((a : ℝ) / Fintype.card {x // isV x = true}) ^ s.card *
        (1 + (b : ℝ) / Fintype.card {x // ¬ isV x = true}) ^ z.card) ≤
      (∑ d : Index isV a b,
        (∏ i ∈ s, (d.val i : ℝ)) * (∏ i ∈ z, ((d.val i : ℝ) + 1))) /
        (Fintype.card (Index isV a b) : ℝ) := by
  rw [bidegree_average_eq_occupationAverage_fintype isV a b
    (fun M => ∏ i ∈ s, (M i : ℝ))
    (fun M => ∏ i ∈ z, ((M i : ℝ) + 1))]
  have h := occupation_first_moment_lower a b s z ha hb hs hz
  rw [occupationAverage_tensor] at h
  exact h

end Problem335.BidegreeAverages

end

end OAI
