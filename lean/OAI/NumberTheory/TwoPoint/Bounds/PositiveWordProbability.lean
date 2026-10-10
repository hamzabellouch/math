import OAI.NumberTheory.TwoPoint.Walks.ProhibitedCircuit
import OAI.NumberTheory.TwoPoint.Bounds.UniformResidues
import OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling
import OAI.NumberTheory.TwoPoint.Bounds.CrudeWordCounting

namespace OAI

/-!
# Probability of one positive numerical word

The same residue coordinate is reused at every occurrence of a prime.
Selecting one occurrence per distinct prime therefore bounds the probability
by one reciprocal per distinct prime, including all padding factors. There
is no independence assumption between different sites of the word.
-/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma FiniteLaw.probability_mono_of_imp {A : Type*} [Fintype A]
    (μ : FiniteLaw A) {E F : A → Prop} (h : ∀ x, E x → F x) :
    μ.probability E ≤ μ.probability F := by
  apply μ.average_mono
  intro x
  by_cases he : E x
  · simp only [ite_eq_left he, ite_eq_left (h x he), le_refl]
  · simp only [ite_eq_right he]
    split_ifs <;> norm_num

/-- Every residue modulo the true modulus has precisely its uniform mass,
even though the common carrier `Fin B` also contains zero-weight points. -/
theorem uniformResidueLaw_mod_eq (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B) (r : ZMod p) :
    (uniformResidueLaw B p hp hpB).probability
      (fun x => (x.val : ZMod p) = r) = (p : ℝ)⁻¹ := by
  classical
  let : NeZero p := ⟨hp.ne'⟩
  let : DecidableEq (ZMod p) := fun _ _ => Classical.propDecidable _
  let a : Fin B := ⟨r.val, r.val_lt.trans_le hpB⟩
  have ha : a.val < p := r.val_lt
  have har : (a.val : ZMod p) = r := ZMod.natCast_zmod_val r
  have hterm (x : Fin B) :
      (uniformResidueLaw B p hp hpB).weight x *
        (if (x.val : ZMod p) = r then (1 : ℝ) else 0) =
      if x = a then (p : ℝ)⁻¹ else 0 := by
    by_cases hx : x = a
    · subst x
      simp only [uniformResidueLaw_weight B p hp hpB a ha, har, ite_true, mul_one]
    · by_cases hxp : x.val < p
      · have hxr : (x.val : ZMod p) ≠ r := by
          intro he
          have hv := congrArg ZMod.val he
          rw [ZMod.val_natCast_of_lt hxp] at hv
          exact hx (Fin.ext hv)
        simp only [uniformResidueLaw_weight B p hp hpB x hxp, ite_eq_right hxr,
          mul_zero, ite_eq_right hx]
      · simp only [uniformResidueLaw, ite_eq_right hxp, zero_mul, ite_eq_right hx]
  unfold FiniteLaw.probability FiniteLaw.average
  dsimp only
  calc
    _ = ∑ x : Fin B, if x = a then (p : ℝ)⁻¹ else 0 :=
      Finset.sum_congr rfl (fun x _ => hterm x)
    _ = _ := by simp

/-- Distinct prime factors in all the step divisors, both tuples and padding. -/
def wordDivisorPrimeSupport (w : List SignedStep) : Finset ℕ :=
  w.toFinset.biUnion (fun a => (a.padding * a.tuple).primeFactors)

lemma mem_wordDivisorPrimeSupport (w : List SignedStep) (p : ℕ) :
    p ∈ wordDivisorPrimeSupport w ↔
      ∃ k : Fin w.length, p ∈ ((w.get k).padding * (w.get k).tuple).primeFactors := by
  simp only [wordDivisorPrimeSupport, mem_biUnion, List.mem_toFinset]
  exact List.exists_mem_iff_get

/-- Positivity expressed in the one common set of residue coordinates. -/
def ResiduePositiveWord {ι : Type*} (p : ι → ℕ) (h : ℕ) (w : List SignedStep)
    (r : ∀ i, ZMod (p i)) : Prop :=
  ∀ (k : Fin w.length) (i : ι),
    p i ∈ ((w.get k).padding * (w.get k).tuple).primeFactors →
      r i = -((wordDisplacement h (w.take k.val) : ℤ) : ZMod (p i))

/-- A residue test is exact arithmetic positivity at any common integer lift. -/
theorem residuePositiveWord_iff {ι : Type*} (p : ι → ℕ) (h : ℕ)
    (w : List SignedStep) (r : ∀ i, ZMod (p i)) (n : ℤ)
    (hn : ∀ i, (n : ZMod (p i)) = r i)
    (hsq : ∀ a ∈ w, Squarefree (a.padding * a.tuple))
    (hcover : ∀ q ∈ wordDivisorPrimeSupport w, ∃ i, p i = q) :
    ResiduePositiveWord p h w r ↔ PositiveWord h n w := by
  rw [positiveWord_iff_prime_tests h n w hsq]
  constructor
  · intro hr k q hq
    have hmem : q ∈ wordDivisorPrimeSupport w :=
      (mem_wordDivisorPrimeSupport w q).mpr ⟨k, hq⟩
    obtain ⟨i, rfl⟩ := hcover q hmem
    exact (residue_offset_divisibility (r i) n _ (hn i)).mpr (hr k i hq)
  · intro hn' k i hi
    exact (residue_offset_divisibility (r i) n _ (hn i)).mp (hn' k (p i) hi)

/-- One reciprocal factor for every used residue coordinate. Repeated
occurrences can only make the event smaller, by adding compatibility tests. -/
theorem residuePositiveWord_probability_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℕ) (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (h : ℕ) (w : List SignedStep) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
      (fun x => ResiduePositiveWord p h w (fun i => ((x i).val : ZMod (p i)))) ≤
      ∏ i ∈ univ.filter (fun i => p i ∈ wordDivisorPrimeSupport w), (p i : ℝ)⁻¹ := by
  let E : ∀ i, Fin B → Prop := fun i x => ∀ k : Fin w.length,
    p i ∈ ((w.get k).padding * (w.get k).tuple).primeFactors →
      (x.val : ZMod (p i)) = -((wordDisplacement h (w.take k.val) : ℤ) : ZMod (p i))
  have he : (fun x : ι → Fin B => ResiduePositiveWord p h w
      (fun i => ((x i).val : ZMod (p i)))) = (fun x => ∀ i, E i (x i)) := by
    funext x
    exact propext (forall_comm)
  rw [he, FiniteLaw.independent_probability_all]
  rw [prod_filter]
  apply prod_le_prod₀
  · intro i _
    exact FiniteLaw.probability_nonneg _ _
  · intro i _
    by_cases hi : p i ∈ wordDivisorPrimeSupport w
    · rw [ite_eq_left hi]
      obtain ⟨k, hk⟩ := (mem_wordDivisorPrimeSupport w (p i)).mp hi
      exact ((uniformResidueLaw B (p i) (hp i) (hpB i)).probability_mono_of_imp
        (fun x hx => hx k hk)).trans_eq
          (uniformResidueLaw_mod_eq B (p i) (hp i) (hpB i)
            (-((wordDisplacement h (w.take k.val) : ℤ) : ZMod (p i))))
    · rw [ite_eq_right hi]
      exact FiniteLaw.probability_le_one _ _

/-- For an injectively indexed prime pool covering every step factor, the
bound is literally the product over distinct numerical primes in the word. -/
theorem residuePositiveWord_probability_distinct_primes {ι : Type*}
    [Fintype ι] [DecidableEq ι] (B : ℕ) (p : ι → ℕ)
    (hinj : Function.Injective p) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (h : ℕ) (w : List SignedStep)
    (hcover : ∀ q ∈ wordDivisorPrimeSupport w, ∃ i, p i = q) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
      (fun x => ResiduePositiveWord p h w (fun i => ((x i).val : ZMod (p i)))) ≤
      ∏ q ∈ wordDivisorPrimeSupport w, (q : ℝ)⁻¹ := by
  have himage : (univ.filter (fun i => p i ∈ wordDivisorPrimeSupport w)).image p =
      wordDivisorPrimeSupport w := by
    ext q
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hq
      obtain ⟨i, rfl⟩ := hcover q hq
      exact ⟨i, hq, rfl⟩
  have hbound := residuePositiveWord_probability_le B p hp hpB h w
  rw [← himage, prod_image (fun i _ j _ hij => hinj hij)]
  exact hbound

/-- The finite catalog's modular event is exactly the deleted event at any
common integer lift. Minimality remains in the catalog, not in the random law. -/
theorem prohibited_residue_catalog_iff {ι : Type*} (p : ι → ℕ)
    (pairs : Finset (ℕ × ℕ)) (h s : ℕ) (r : ∀ i, ZMod (p i)) (n : ℤ)
    (hn : ∀ i, (n : ZMod (p i)) = r i)
    (hsq : ∀ dq ∈ pairs, Squarefree (dq.2 * dq.1))
    (hcover : ∀ c : ProhibitedCatalog pairs h s,
      ∀ q ∈ wordDivisorPrimeSupport (decodeStepWord c.val), ∃ i, p i = q) :
    (∃ c : ProhibitedCatalog pairs h s, ResiduePositiveWord p h (decodeStepWord c.val) r) ↔
      ProhibitedSite h s (fun d q => (d, q) ∈ pairs) n := by
  have he (c : ProhibitedCatalog pairs h s) :
      ResiduePositiveWord p h (decodeStepWord c.val) r ↔
        PositiveWord h n (decodeStepWord c.val) :=
    residuePositiveWord_iff p h _ r n hn
      (fun a ha => hsq _ (c.property.1.2.2.1 a ha)) (hcover c)
  simp_rw [he]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨decodeStepWord c.val, hc, c.property⟩
  · rintro ⟨w, hw, hmin⟩
    obtain ⟨c, hc⟩ := stepWord_covered pairs s w hmin.1.2.1 hmin.1.2.2.1
    refine ⟨⟨c, ?_⟩, ?_⟩
    · simpa only [hc] using hmin
    · simpa only [hc] using hw

/-- A literal union bound for the actual minimal-word catalog. The remaining
arithmetic task is to sum these distinct-prime weights over that catalog. -/
theorem prohibited_residue_probability_le_catalog {ι : Type*}
    [Fintype ι] [DecidableEq ι] (B : ℕ) (p : ι → ℕ)
    (hinj : Function.Injective p) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (pairs : Finset (ℕ × ℕ)) (h s : ℕ)
    (hcover : ∀ c : ProhibitedCatalog pairs h s,
      ∀ q ∈ wordDivisorPrimeSupport (decodeStepWord c.val), ∃ i, p i = q) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
      (fun x => ∃ c : ProhibitedCatalog pairs h s,
        ResiduePositiveWord p h (decodeStepWord c.val)
          (fun i => ((x i).val : ZMod (p i)))) ≤
      ∑ c : ProhibitedCatalog pairs h s,
        ∏ q ∈ wordDivisorPrimeSupport (decodeStepWord c.val), (q : ℝ)⁻¹ := by
  apply (FiniteLaw.probability_exists_le _ _).trans
  apply sum_le_sum
  intro c _
  exact residuePositiveWord_probability_distinct_primes B p hinj hp hpB h _ (hcover c)

end TwoPointCorrelations

end OAI
