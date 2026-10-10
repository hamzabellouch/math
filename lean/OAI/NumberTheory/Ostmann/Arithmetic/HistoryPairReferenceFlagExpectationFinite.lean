import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationBasic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction Construction.CanonicalOccurrenceTransport HistoryPairPattern
attribute [local instance] Classical.propDecidable

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ} {α β : Type*} [Fintype α] [Fintype β]

def activeMean (μ : α → ℝ) (ν w : α → β → ℝ) (active : α → Prop)
    (D E : (i : α) → active i → DecodedDraw sources seed V outside l)
    (x : (i : α) → (hi : active i) → β → PairKey (D i hi).history (E i hi).history → ℤ) : ℝ :=
  ∑ i, μ i * if hi : active i then ∑ j, ν i j * w i j * family (D i hi) (E i hi) (x i hi j) else 0

def fixedSamples (active : α → Prop)
    (D E : (i : α) → active i → DecodedDraw sources seed V outside l)
    (D0 E0 : DecodedDraw sources seed V outside l)
    (hp : ∀ i hi, SamePairPattern seed (D i hi).history (E i hi).history D0.history E0.history
      (D i hi).labels (E i hi).labels D0.labels E0.labels)
    (x : (i : α) → (hi : active i) → β → PairKey (D i hi).history (E i hi).history → ℤ)
    (inactive : α → β → PairKey D0.history E0.history → ℤ)
    (i : α) (j : β) : PairKey D0.history E0.history → ℤ :=
  if hi : active i then pullSample (D i hi) (E i hi) D0 E0 (hp i hi) (x i hi j) else inactive i j

theorem activeMean_eq_fixed (μ : α → ℝ) (ν w : α → β → ℝ) (active : α → Prop)
    (D E : (i : α) → active i → DecodedDraw sources seed V outside l)
    (D0 E0 : DecodedDraw sources seed V outside l)
    (hD : ∀ i hi, (D i hi).SameFrequencies D0)
    (hE : ∀ i hi, (E i hi).SameFrequencies E0)
    (hp : ∀ i hi, SamePairPattern seed (D i hi).history (E i hi).history D0.history E0.history
      (D i hi).labels (E i hi).labels D0.labels E0.labels)
    (x : (i : α) → (hi : active i) → β → PairKey (D i hi).history (E i hi).history → ℤ)
    (inactive : α → β → PairKey D0.history E0.history → ℤ) :
    activeMean μ ν w active D E x =
      ∑ i, μ i * if _hi : active i then ∑ j, ν i j * w i j *
        family D0 E0 (fixedSamples active D E D0 E0 hp x inactive i j) else 0 := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : active i
  · simp only [dite_eq_left hi,fixedSamples]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [family_eq_pullSample (D i hi) (E i hi) D0 E0 (hD i hi) (hE i hi) (hp i hi)]
  · simp only [dite_eq_right hi,mul_zero]

theorem activeMean_le_fixed (μ : α → ℝ) (ν w : α → β → ℝ) (active : α → Prop)
    (D E : (i : α) → active i → DecodedDraw sources seed V outside l)
    (D0 E0 : DecodedDraw sources seed V outside l)
    (hD : ∀ i hi, (D i hi).SameFrequencies D0)
    (hE : ∀ i hi, (E i hi).SameFrequencies E0)
    (hp : ∀ i hi, SamePairPattern seed (D i hi).history (E i hi).history D0.history E0.history
      (D i hi).labels (E i hi).labels D0.labels E0.labels)
    (x : (i : α) → (hi : active i) → β → PairKey (D i hi).history (E i hi).history → ℤ)
    (inactive : α → β → PairKey D0.history E0.history → ℤ)
    (A : ℝ) (hA : 0 ≤ A) (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i j, 0 ≤ ν i j)
    (hw : ∀ i, active i → μ i ≠ 0 → ∀ j, ν i j ≠ 0 → w i j ≤ A) :
    activeMean μ ν w active D E x ≤
      A * ∑ i, μ i * ∑ j, ν i j * family D0 E0 (fixedSamples active D E D0 E0 hp x inactive i j) := by
  rw [activeMean_eq_fixed μ ν w active D E D0 E0 hD hE hp x inactive,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hm : μ i=0
  · simp only [hm,zero_mul,mul_zero,le_refl]
  rw [← mul_assoc,mul_comm A (μ i),mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (hμ i)
  by_cases hi : active i
  · rw [dite_eq_left hi,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hn : ν i j=0
    · simp only [hn,zero_mul,mul_zero,le_refl]
    calc
      ν i j * w i j * family D0 E0 _ ≤ ν i j * A * family D0 E0 _ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hw i hi hm j hn) (hν i j))
          (family_nonneg D0 E0 _)
      _ = A * (ν i j * family D0 E0 _) := by ring
  · rw [dite_eq_right hi]
    exact mul_nonneg hA (Finset.sum_nonneg (fun j _ => mul_nonneg (hν i j) (family_nonneg D0 E0 _)))

theorem activeMean_zero_of_inactive (μ : α → ℝ) (ν w : α → β → ℝ) (active : α → Prop)
    (D E : (i : α) → active i → DecodedDraw sources seed V outside l)
    (x : (i : α) → (hi : active i) → β → PairKey (D i hi).history (E i hi).history → ℤ)
    (h : ∀ i, ¬ active i) : activeMean μ ν w active D E x=0 := by
  apply Finset.sum_eq_zero
  intro i _
  simp [h i]

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
