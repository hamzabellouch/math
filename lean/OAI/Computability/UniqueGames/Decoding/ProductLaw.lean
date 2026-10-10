import OAI.Computability.UniqueGames.Foundations.Conditioning
import OAI.Computability.UniqueGames.Soundness.ConditionalReindex

namespace OAI

section

/-!
# Weighted conditional product law for the v2 clean coordinates

The equation distribution is arbitrary.  All identities below are identities
of finite sums of its actual weights, rather than a reduction to uniform
occurrence sampling.  The clean set is fixed by independently sampled advice;
the only subsequently exposed question data lie outside that set.  Conditioning
on such data preserves the entire joint law of the clean questions.
-/

namespace UniqueGamesTheorem.Clean.ProductLaw

open scoped BigOperators
open Foundations.Games
open Soundness.ConditionalIncidences

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P Q S : Type} [Fintype P] [DecidableEq P] [Fintype Q] [Fintype S]

/-- Restriction to the clean and nonclean coordinates is a genuine bijection. -/
def splitCoordinates (K : Finset P) :
    (P → Q) ≃ (PositionInside K → Q) × (PositionOutside K → Q) :=
  Equiv.piEquivPiSubtypeProd (fun i => i ∈ K) (fun _ => Q)

/-- Independent weighted sampling splits into independent clean and nonclean
parts. This identity proves, rather than assumes, their independence. -/
theorem table_split (μ : P → FiniteDistribution Q) (K : Finset P) :
    (FiniteDistribution.table μ).transport (splitCoordinates K) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).product
        (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro pieces
  change (∏ i, (μ i).weight ((splitCoordinates K).symm pieces i)) =
    (∏ i : PositionInside K, (μ i.val).weight (pieces.1 i)) *
      ∏ i : PositionOutside K, (μ i.val).weight (pieces.2 i)
  have h := Fintype.prod_subtype_mul_prod_subtype (fun i : P => i ∈ K)
    (fun i => (μ i).weight ((splitCoordinates K).symm pieces i))
  have hi : Subtype.fintype (fun i : P => i ∈ K) =
      Finset.Subtype.fintype K := Subsingleton.elim _ _
  rw [hi] at h
  calc
    _ = (∏ i : PositionInside K,
        (μ i.val).weight ((splitCoordinates K).symm pieces i.val)) *
        ∏ i : PositionOutside K,
          (μ i.val).weight ((splitCoordinates K).symm pieces i.val) := h.symm
    _ = _ := by
      congr 1 <;> apply Finset.prod_congr rfl <;> intro i _ <;>
        simp [splitCoordinates, Equiv.piEquivPiSubtypeProd, i.property]

theorem probability_product_and (μ : FiniteDistribution Q) (ν : FiniteDistribution S)
    (event : Q → Bool) (given : S → Bool) :
    (μ.product ν).probability (fun x => event x.1 && given x.2) =
      μ.probability event * ν.probability given := by
  classical
  simp only [FiniteDistribution.probability, FiniteDistribution.product,
    Fintype.sum_prod_type]
  calc
    _ = ∑ q, ∑ s, (if event q then μ.weight q else 0) *
        (if given s then ν.weight s else 0) := by
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro s _
      cases event q <;> cases given s <;> simp
    _ = _ := by rw [Finset.sum_mul_sum]

theorem probability_product_right (μ : FiniteDistribution Q)
    (ν : FiniteDistribution S) (given : S → Bool) :
    (μ.product ν).probability (fun x => given x.2) = ν.probability given := by
  simpa using probability_product_and μ ν (fun _ => true) given

/-- Exact factorization for an arbitrary joint event of clean coordinates and
an arbitrary observation/event depending only on the nonclean coordinates. -/
theorem table_inside_outside (μ : P → FiniteDistribution Q) (K : Finset P)
    (event : (PositionInside K → Q) → Bool)
    (given : (PositionOutside K → Q) → Bool) :
    (FiniteDistribution.table μ).probability
        (fun x => event (fun i => x i.val) && given (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event *
        (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)).probability given := by
  rw [← probability_product_and, ← table_split]
  exact (FiniteDistribution.probability_transport (FiniteDistribution.table μ)
    (splitCoordinates K) (fun pieces => event pieces.1 && given pieces.2)).symm

theorem table_outside (μ : P → FiniteDistribution Q) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool) :
    (FiniteDistribution.table μ).probability (fun x => given (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)).probability given := by
  simpa using table_inside_outside μ K (fun _ => true) given

/-- The normalized conditional law is the ordinary independent product law.
The only hypothesis is that the observed outside event has positive mass. -/
theorem conditioned_inside (μ : P → FiniteDistribution Q) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool)
    (positive : 0 < (FiniteDistribution.table μ).probability
      (fun x => given (fun i => x i.val)))
    (event : (PositionInside K → Q) → Bool) :
    ((FiniteDistribution.table μ).condition
      (fun x => given (fun i => x i.val)) positive).probability
        (fun x => event (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event := by
  rw [FiniteDistribution.probability_condition]
  simp_rw [Bool.and_comm (given _)]
  rw [table_inside_outside, table_outside]
  have hne : (FiniteDistribution.table
      (fun i : PositionOutside K => μ i.val)).probability given ≠ 0 := by
    rw [table_outside] at positive
    exact ne_of_gt positive
  exact mul_div_cancel_right₀ _ hne

/-- Fixing an independently sampled seed additionally exposes the intercept and
all slope data, without exposing any of the clean questions. The seed's mass
and the outside-observation mass factor off from every clean event. -/
theorem seeded_inside_outside (ν : FiniteDistribution S)
    (μ : P → FiniteDistribution Q) (seed : S) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool)
    (event : (PositionInside K → Q) → Bool) :
    (ν.product (FiniteDistribution.table μ)).probability
      (fun x => (decide (x.1 = seed) && given (fun i => x.2 i.val)) &&
        event (fun i => x.2 i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event *
        (ν.weight seed *
          (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)).probability given) := by
  simp_rw [Bool.and_assoc, Bool.and_comm (given _)]
  rw [probability_product_and ν (FiniteDistribution.table μ)
    (fun s => decide (s = seed))
    (fun x : P → Q => event (fun i => x i.val) && given (fun i => x i.val)),
    table_inside_outside]
  have hseed : ν.probability (fun s => decide (s = seed)) = ν.weight seed := by
    simp [FiniteDistribution.probability]
  rw [hseed]
  ring

/-- Public conditioning on the independently generated advice, including its
intercept, and on arbitrary nonclean question data leaves the weighted clean
product law unchanged. `K` may be any function of `seed`; it is fixed here after
the public seed has been exposed. -/
theorem conditioned_seed_inside (ν : FiniteDistribution S)
    (μ : P → FiniteDistribution Q) (seed : S) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool)
    (positive : 0 < (ν.product (FiniteDistribution.table μ)).probability
      (fun x => decide (x.1 = seed) && given (fun i => x.2 i.val)))
    (event : (PositionInside K → Q) → Bool) :
    ((ν.product (FiniteDistribution.table μ)).condition
      (fun x => decide (x.1 = seed) && given (fun i => x.2 i.val)) positive).probability
        (fun x => event (fun i => x.2 i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event := by
  have hgiven := seeded_inside_outside ν μ seed K given (fun _ => true)
  simp only [Bool.and_true, FiniteDistribution.probability_true, one_mul] at hgiven
  rw [FiniteDistribution.probability_condition, seeded_inside_outside, hgiven]
  exact mul_div_cancel_right₀ _ (ne_of_gt (hgiven ▸ positive))

/-- Reindexing a finite coordinate set gives the usual `iid` law on `Fin r`. -/
theorem table_reindex (μ : FiniteDistribution Q) {A : Type} [Fintype A] [DecidableEq A]
    {r : ℕ} (e : Fin r ≃ A) :
    (FiniteDistribution.table (fun _ : A => μ)).transport (coordinateReindex e) =
      μ.iid r := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ a, μ.weight (x (e.symm a))) = ∏ i, μ.weight (x i)
  exact e.symm.prod_comp (fun i => μ.weight (x i))

/-- Fixed advice, intercept and nonclean data preserve precisely the repeated
incidence law for arbitrary occurrence weights. Repeated IDs are permitted. -/
theorem conditioned_incidence_reindex
    {O N D : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    [Zero D] [DecidableEq D]
    (μ : FiniteDistribution (O × Fin 3))
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed)))
    {r : ℕ} (e : Fin r ≃ PositionInside (zeroSet J gamma))
    (event : (Fin r → O × N) → Bool) :
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed))
        positive).probability
          (fun x => event (fun i => incidence name (x (e i).val))) =
      ((μ.pushforward (incidence name)).iid r).probability event := by
  classical
  let given : (PositionOutside (zeroSet J gamma) → O × Fin 3) → Bool :=
    fun x => decide ((fun i => incidence name (x i)) = observed)
  let insideEvent : (PositionInside (zeroSet J gamma) → O × Fin 3) → Bool :=
    fun x => event (fun i => incidence name (x (e i)))
  have h := conditioned_inside (fun _ : P => μ) (zeroSet J gamma)
    given positive insideEvent
  change _ = _ at h
  rw [FiniteDistribution.iid_pushforward, FiniteDistribution.probability_pushforward]
  rw [← table_reindex μ e, FiniteDistribution.probability_transport]
  exact h

/-- Equality of the complete conditional question distribution, not only its
individual marginals. The target is the ordinary repeated incidence law. -/
theorem conditioned_incidence_distribution
    {O N D : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    [Zero D] [DecidableEq D]
    (μ : FiniteDistribution (O × Fin 3))
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed)))
    {r : ℕ} (e : Fin r ≃ PositionInside (zeroSet J gamma)) :
    (((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed))
        positive).pushforward
          (fun x i => incidence name (x (e i).val))) =
      (μ.pushforward (incidence name)).iid r := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro questions
  have h := conditioned_incidence_reindex μ J name gamma observed positive e
    (fun x => decide (x = questions))
  calc
    _ = ((FiniteDistribution.table (fun _ : P => μ)).condition
        (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed)) positive).probability
          (fun x => decide ((fun i => incidence name (x (e i).val)) = questions)) := by
      unfold FiniteDistribution.pushforward FiniteDistribution.probability
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : (fun i => incidence name (x (e i).val)) = questions <;> simp [hx]
    _ = _ := h
    _ = _ := by simp [FiniteDistribution.probability]

omit [Fintype P] in
/-- A clean-mask rule reads only the independent advice seed. Thus even after
fixing the entire question tuple, its distribution is unchanged. The seed may
include the projection mask, all slope columns, and the independent intercept. -/
theorem clean_mask_independent (ν : FiniteDistribution S)
    (μ : FiniteDistribution Q) (clean : S → Finset P) (K : Finset P)
    (questionEvent : Q → Bool) :
    (ν.product μ).probability (fun x => decide (clean x.1 = K) && questionEvent x.2) =
      ν.probability (fun s => decide (clean s = K)) * μ.probability questionEvent := by
  exact probability_product_and ν μ (fun s => decide (clean s = K)) questionEvent

end
end UniqueGamesTheorem.Clean.ProductLaw

end

end OAI
