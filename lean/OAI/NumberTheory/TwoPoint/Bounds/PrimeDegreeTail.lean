import OAI.NumberTheory.TwoPoint.Bounds.PositivePrimeTilt
import OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingResidues
import OAI.NumberTheory.TwoPoint.Bounds.ResidueRestriction

namespace OAI

/-! The prime-degree deletion under the literal full residue law.  The
positive tuple majorant has mean `2^omega(d)/d`, and its tilted degree
tail is exponentially small in `W * omega(d)`. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def primeSelection (P S : Finset ℕ) (hSP : S ⊆ P) : Finset P :=
  S.attach.image (fun p => (⟨p.val, hSP p.property⟩ : P))

lemma primeSelection_card (P S : Finset ℕ) (hSP : S ⊆ P) :
    (primeSelection P S hSP).card = S.card := by
  have hi : Function.Injective (fun p : S => (⟨p.val, hSP p.property⟩ : P)) := by
    intro p q hpq
    exact Subtype.ext (congrArg (fun r : P => r.val) hpq)
  simp only [primeSelection, card_image_of_injective _ hi, card_attach]

noncomputable def positivePrimeWeight (S : Finset ℕ) (n : ℤ) : ℝ :=
  ∏ p ∈ S, ((if (p : ℤ) ∣ n then 1 else 0) + 1 / (p : ℝ))

noncomputable def positivePrimeNormalizer (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S, 2 / (p : ℝ)

lemma positivePrimeWeight_nonneg (S : Finset ℕ) (n : ℤ) :
    0 ≤ positivePrimeWeight S n := by
  apply prod_nonneg
  intro p _
  split_ifs <;> positivity

lemma abs_centeredTuple_le_positivePrimeWeight (S : Finset ℕ) (n : ℤ) :
    |centeredTuple S n| ≤ positivePrimeWeight S n := by
  rw [centeredTuple, abs_prod]
  apply prod_le_prod₀ (fun _ _ => abs_nonneg _)
  intro p _
  have hi : 0 ≤ (if (p : ℤ) ∣ n then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hp : 0 ≤ (p : ℝ)⁻¹ := by positivity
  simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hi, abs_of_nonneg hp, one_div] using
    abs_sub_le (if (p : ℤ) ∣ n then (1 : ℝ) else 0) 0 (p : ℝ)⁻¹

lemma positivePrimeWeight_eq_selection (P S : Finset ℕ) (hSP : S ⊆ P) (n : ℤ) :
    positivePrimeWeight S n =
      positiveCenterWeight (fun p : P => 1 / (p.val : ℝ)) (primeSelection P S hSP)
        (fun p => decide ((p.val : ℤ) ∣ n)) := by
  rw [positiveCenterWeight_eq]
  unfold primeSelection
  rw [prod_image]
  · simp only [positivePrimeWeight, decide_eq_true_eq]
    exact (prod_attach S (fun p : ℕ =>
      (if (p : ℤ) ∣ n then (1 : ℝ) else 0) + 1 / (p : ℝ))).symm
  · intro p _ q _ hpq
    exact Subtype.ext (congrArg (fun r : P => r.val) hpq)

lemma positivePrimeNormalizer_eq_selection (P S : Finset ℕ) (hSP : S ⊆ P) :
    positivePrimeNormalizer S =
      positiveCenterNormalizer (fun p : P => 1 / (p.val : ℝ)) (primeSelection P S hSP) := by
  rw [positiveCenterNormalizer_eq]
  unfold primeSelection
  rw [prod_image]
  · simp only [positivePrimeNormalizer, mul_one_div]
    exact (prod_attach S (fun p : ℕ => (2 : ℝ) / p)).symm
  · intro p _ q _ hpq
    exact Subtype.ext (congrArg (fun r : P => r.val) hpq)

lemma positivePrimeNormalizer_squarefree (d : ℕ) (hd : Squarefree d) :
    positivePrimeNormalizer d.primeFactors = (2 : ℝ) ^ d.primeFactors.card / d := by
  unfold positivePrimeNormalizer
  rw [prod_div_distrib, prod_const]
  congr 1
  rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]

lemma actualPrimeDegree_eq_count (P : Finset ℕ) (n : ℤ) :
    (actualPaddingDegree P n : ℝ) =
      booleanCount (fun p : P => decide ((p.val : ℤ) ∣ n)) := by
  rw [actualPaddingDegree_eq_available, paddingAvailablePrimes_card, booleanCount_eq_card]
  rfl

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

/-- Every prime coordinate retains its Bernoulli divisibility law under
the full tuple-and-padding law, also at a translated CRT origin. -/
lemma residue_average_prime_availability
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (site : ℤ)
    (F : (data.P → Bool) → ℝ) :
    (data.residueLaw B hB).average (fun x =>
      F (fun p : data.P => decide ((p.val : ℤ) ∣ data.residueOrigin x + site))) =
      (paddingOriginalLaw data.P (fun p hp => (data.primeP p hp).two_le)).average F := by
  let e : data.P → ↥(data.P ∪ data.Q) := fun p => ⟨p.val, mem_union_left _ p.property⟩
  have he : Function.Injective e := by
    intro p q hpq
    exact Subtype.ext (congrArg (fun r : ↥(data.P ∪ data.Q) => r.val) hpq)
  calc
    _ = (data.residueLaw B hB).average (fun x =>
        F (paddingResidueAvailable data.P B site (fun p => x (e p)))) := by
      apply congrArg (data.residueLaw B hB).average
      funext x
      apply congrArg F
      funext p
      change decide ((p.val : ℤ) ∣ data.residueOrigin x + site) =
        decide ((p.val : ℤ) ∣ (x (e p)).val + site)
      have hdiv : (p.val : ℤ) ∣ data.residueOrigin x + site ↔
          (p.val : ℤ) ∣ (x (e p)).val + site := data.residueOrigin_divisibility x (e p) site
      simp only [hdiv]
    _ = (FiniteLaw.independent (fun p : data.P => uniformResidueLaw B p.val
        (data.primeP p p.property).pos (hB p (mem_union_left _ p.property)))).average
          (fun z => F (paddingResidueAvailable data.P B site z)) :=
      FiniteLaw.independent_average_embedding e he
        (fun p => uniformResidueLaw B p.val (data.prime p).pos (hB p p.property))
        (fun z => F (paddingResidueAvailable data.P B site z))
    _ = _ := padding_residue_average data.P B (fun p hp => (data.primeP p hp).two_le)
      (fun p hp => hB p (mem_union_left _ hp)) site F

lemma positive_prime_mean (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (S : Finset ℕ) (hSP : S ⊆ data.P) (site : ℤ) :
    (data.residueLaw B hB).average
      (fun x => positivePrimeWeight S (data.residueOrigin x + site)) =
        positivePrimeNormalizer S := by
  let q := fun p : data.P => 1 / (p.val : ℝ)
  let T := primeSelection data.P S hSP
  have hq0 (p : data.P) : 0 ≤ q p := by dsimp [q]; positivity
  have hq1 (p : data.P) : q p ≤ 1 := by
    apply (div_le_one (by exact_mod_cast (data.primeP p p.property).pos)).mpr
    exact_mod_cast (data.primeP p p.property).one_lt.le
  simp_rw [positivePrimeWeight_eq_selection data.P S hSP]
  rw [data.residue_average_prime_availability hB site (positiveCenterWeight q T)]
  exact (positive_center_tilt_total q T hq0 hq1).trans
    (positivePrimeNormalizer_eq_selection data.P S hSP).symm

/-- The positive centered-prime majorant, with a prime-degree failure,
is bounded by its exact mean times `exp(-2W * #S)`. -/
theorem positive_prime_degree_tail (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (S : Finset ℕ) (hSP : S ⊆ data.P) (W : ℝ) (hW : 10 ≤ W)
    (hmass : (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * S.card) (site : ℤ) :
    (data.residueLaw B hB).average (fun x =>
      positivePrimeWeight S (data.residueOrigin x + site) *
        if 6 * W * S.card < (actualPaddingDegree data.P (data.residueOrigin x + site) : ℝ)
          then 1 else 0) ≤
      positivePrimeNormalizer S * Real.exp (-2 * W * S.card) := by
  let q := fun p : data.P => 1 / (p.val : ℝ)
  let T := primeSelection data.P S hSP
  have hq0 (p : data.P) : 0 ≤ q p := by dsimp [q]; positivity
  have hq1 (p : data.P) : q p ≤ 1 := by
    apply (div_le_one (by exact_mod_cast (data.primeP p p.property).pos)).mpr
    exact_mod_cast (data.primeP p p.property).one_lt.le
  have hm : (∑ p : data.P, q p) ≤ 2 * W * T.card := by
    rw [primeSelection_card]
    change (∑ p : data.P, 1 / (p.val : ℝ)) ≤ 2 * W * S.card
    rw [sum_coe_sort data.P (fun p : ℕ => 1 / (p : ℝ))]
    exact hmass
  have he (x : ↥(data.P ∪ data.Q) → Fin B) :
      positivePrimeWeight S (data.residueOrigin x + site) *
        (if 6 * W * S.card < (actualPaddingDegree data.P (data.residueOrigin x + site) : ℝ)
          then (1 : ℝ) else 0) =
      positiveCenterWeight q T (fun p : data.P =>
        decide ((p.val : ℤ) ∣ data.residueOrigin x + site)) *
        (if 6 * W * T.card < booleanCount (fun p : data.P =>
          decide ((p.val : ℤ) ∣ data.residueOrigin x + site)) then 1 else 0) := by
    rw [positivePrimeWeight_eq_selection data.P S hSP,
      actualPrimeDegree_eq_count, primeSelection_card]
  simp_rw [he]
  rw [data.residue_average_prime_availability hB site (fun a =>
    positiveCenterWeight q T a * if 6 * W * T.card < booleanCount a then 1 else 0)]
  have ht := positive_center_weighted_degree_tail q T hq0 hq1 W hW hm
  rw [primeSelection_card, ← positivePrimeNormalizer_eq_selection] at ht
  simpa only [paddingOriginalLaw, paddingOriginalPrimeLaw, T, q, primeSelection_card] using ht

theorem positive_tuple_degree_tail (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (d : ℕ) (hd : Squarefree d) (hdP : d.primeFactors ⊆ data.P)
    (hdJ : d.primeFactors.card = J) (W : ℝ) (hW : 10 ≤ W)
    (hmass : (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * J) (site : ℤ) :
    (data.residueLaw B hB).average (fun x =>
      positivePrimeWeight d.primeFactors (data.residueOrigin x + site) *
        if 6 * W * J < (actualPaddingDegree data.P (data.residueOrigin x + site) : ℝ)
          then 1 else 0) ≤
      ((2 : ℝ) ^ J / d) * Real.exp (-2 * W * J) := by
  have ht := data.positive_prime_degree_tail hB d.primeFactors hdP W hW
    (by simpa only [hdJ] using hmass) site
  simpa only [positivePrimeNormalizer_squarefree d hd, hdJ] using ht

end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI
