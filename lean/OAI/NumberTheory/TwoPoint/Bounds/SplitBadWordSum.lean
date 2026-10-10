import OAI.NumberTheory.TwoPoint.Bounds.BadWordRelations
import OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling
import OAI.NumberTheory.TwoPoint.Bounds.PrimeSlotClasses

namespace OAI

/-!
# Summing tuple and padding classes in the required order

The padding assignment is frozen before applying the nondegenerate tuple
relation. It is then averaged with one reciprocal per padding class. The
statement permits different symbolic words for different padding choices,
since every bound is uniform in those choices.
-/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma sum_reciprocal_assignments {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Finset ℕ) :
    (∑ x : ι → P, ∏ i, ((x i).val : ℝ)⁻¹) = primeHarmonicMass P ^ Fintype.card ι := by
  simpa only [prod_const, card_univ, primeHarmonicMass] using
    (Fintype.prod_sum (fun (_ : ι) (p : P) => (p.val : ℝ)⁻¹)).symm

/-- Splitting the class set preserves the original reciprocal product. -/
lemma reciprocal_product_join {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (a : S → ℕ) (b : {i // i ∉ S} → ℕ) :
    (∏ i, ((joinCoordinates S a b i : ℕ) : ℝ)⁻¹) =
      (∏ i : S, (a i : ℝ)⁻¹) * ∏ i : {i // i ∉ S}, (b i : ℝ)⁻¹ := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)]
  simp only [joinCoordinates_mem, joinCoordinates_notMem]
  have hinst : Subtype.fintype (fun i : ι => i ∈ S) = (inferInstance : Fintype S) :=
    Subsingleton.elim _ _
  rw [hinst]

/-- The complete finite weighted estimate for one fixed equality pattern.
Tuple and padding labels remain separate even after numerical enlargement. -/
theorem split_prohibited_reciprocal_bound {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {s J : ℕ} {supply : ℕ → ℕ → Prop}
    (R h : ℕ) (P Q : Finset ℕ) (word : (κ → Q) → LabeledPrimeWord ι)
    (hlen : ∀ b, (word b).word.length ≤ R)
    (hP : ∀ p ∈ P, p.Prime) (hVP : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B) :
    (∑ b : κ → Q, (∏ j, ((b j).val : ℝ)⁻¹) *
      ∑ a : ι → P, if ResampledProhibitedEvent (word b) h s J supply (fun i => (a i).val)
        then ∏ i, ((a i).val : ℝ)⁻¹ else 0) ≤
      (Fintype.card ι ^ 2 * (R + 1) ^ 2 : ℕ) *
        primeHarmonicMass P ^ Fintype.card ι * primeHarmonicMass Q ^ Fintype.card κ *
          ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
  let C : ℝ := (Fintype.card ι ^ 2 * (R + 1) ^ 2 : ℕ) *
    primeHarmonicMass P ^ Fintype.card ι * ((H : ℝ)⁻¹ + (1 + Real.log B) / H)
  have hinner (b : κ → Q) :
      (∑ a : ι → P, if ResampledProhibitedEvent (word b) h s J supply (fun i => (a i).val)
        then ∏ i, ((a i).val : ℝ)⁻¹ else 0) ≤ C :=
    resampled_prohibited_reciprocal_bound R h (word b) (hlen b)
      P hP hVP H B hH hB hlo hhi
  calc
    _ ≤ ∑ b : κ → Q, (∏ j, ((b j).val : ℝ)⁻¹) * C := by
      exact sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hinner b)
        (prod_nonneg (fun j _ => by positivity)))
    _ = (∑ b : κ → Q, ∏ j, ((b j).val : ℝ)⁻¹) * C := (sum_mul _ _ _).symm
    _ = primeHarmonicMass Q ^ Fintype.card κ * C := by
      rw [sum_reciprocal_assignments (ι := κ) Q]
    _ = _ := by dsimp [C]; ring

/-- An actual admissible fiber may contain additional bin, distinctness,
or positivity conditions. Their removal only enlarges this positive sum. -/
theorem split_prohibited_fiber_bound {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {s J : ℕ} {supply : ℕ → ℕ → Prop}
    (R h : ℕ) (P Q : Finset ℕ) (word : (κ → Q) → LabeledPrimeWord ι)
    (hlen : ∀ b, (word b).word.length ≤ R)
    (E : (ι → P) → (κ → Q) → Prop)
    (hE : ∀ a b, E a b →
      ResampledProhibitedEvent (word b) h s J supply (fun i => (a i).val))
    (hP : ∀ p ∈ P, p.Prime) (hVP : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B) :
    (∑ b : κ → Q, ∑ a : ι → P, if E a b then
      (∏ i, ((a i).val : ℝ)⁻¹) * (∏ j, ((b j).val : ℝ)⁻¹) else 0) ≤
      (Fintype.card ι ^ 2 * (R + 1) ^ 2 : ℕ) *
        primeHarmonicMass P ^ Fintype.card ι * primeHarmonicMass Q ^ Fintype.card κ *
          ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
  apply le_trans _ (split_prohibited_reciprocal_bound (s := s) (J := J) (supply := supply)
    R h P Q word hlen
    hP hVP H B hH hB hlo hhi)
  apply sum_le_sum
  intro b _
  rw [mul_sum]
  apply sum_le_sum
  intro a _
  by_cases he : E a b
  · simp only [ite_eq_left he, ite_eq_left (hE a b he)]
    exact le_of_eq (mul_comm _ _)
  · simp only [ite_eq_right he]
    split_ifs <;> positivity

/-- Concrete application to the complete tuple/padding equality code. The
input conditions concern its reconstructed numerical word; the resampling
identity exchanges the order of the two weighted sums. -/
theorem CrudeWordCode.prohibited_fiber_reciprocal_bound {R N s J h : ℕ}
    {supply : ℕ → ℕ → Prop} (c : CrudeWordCode R N R)
    (hc : c.KindConsistent) (hi : c.RowInjective) (P Q : Finset ℕ)
    (E : (c.tupleClasses → P) → ({z : c.usedClasses // z ∉ c.tupleClasses} → Q) → Prop)
    (hE : ∀ a b, E a b →
      let w := c.numericalWord (joinCoordinates c.tupleClasses
        (fun i => (a i).val) (fun j => (b j).val))
      Function.Injective (fun i => (a i).val) ∧
      ForwardProhibited h s supply w ∧
      (∀ t ∈ w, Squarefree t.tuple) ∧
      (∀ t ∈ w, t.tuple.primeFactors.card = J) ∧
      (∀ p j, TuplePrimeAt w p j → ¬p ∣ h ∧ ∀ t ∈ w, ¬p ∣ t.padding))
    (hP : ∀ p ∈ P, p.Prime) (hVP : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B) :
    (∑ b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q,
      ∑ a : c.tupleClasses → P, if E a b then
        (∏ i, ((a i).val : ℝ)⁻¹) * (∏ j, ((b j).val : ℝ)⁻¹) else 0) ≤
      (Fintype.card c.tupleClasses ^ 2 * (R + 1) ^ 2 : ℕ) *
        primeHarmonicMass P ^ Fintype.card c.tupleClasses *
        primeHarmonicMass Q ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} *
          ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
  apply split_prohibited_fiber_bound (s := s) (J := J) (supply := supply) R h P Q
    (fun b => c.labeledWord (fun j => (b j).val))
    (fun b => (c.labeledWord_length _).le) E ?_ hP hVP H B hH hB hlo hhi
  intro a b hab
  have he := hE a b hab
  unfold ResampledProhibitedEvent
  rw [c.labeledWord_resample hc hi]
  exact ⟨he.1, fun i => hP (a i).val (a i).property, he.2⟩

end TwoPointCorrelations

end OAI
