import OAI.NumberTheory.TwoPoint.Bounds.CrudeNumericalWordSum
import OAI.NumberTheory.TwoPoint.Bounds.PaddingResidueEvent

namespace OAI

/-! The padding catalog also pays only one reciprocal per distinct prime. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def paddingOnlyWord {R : ℕ} (q : Fin R → ℕ) : Fin R → SignedStep :=
  fun i => ⟨false, 1, q i⟩

lemma paddingOnlyWord_injective (R : ℕ) :
    Function.Injective (paddingOnlyWord (R := R)) := by
  intro q r h
  funext i
  exact congrArg SignedStep.padding (congrFun h i)

lemma paddingOnlyWord_support {R : ℕ} (q : Fin R → ℕ) :
    wordDivisorPrimeSupport (List.ofFn (paddingOnlyWord q)) = paddingPrimeSupport q := by
  ext p
  simp only [wordDivisorPrimeSupport, List.mem_toFinset, List.mem_ofFn, mem_biUnion,
    paddingPrimeSupport, mem_univ, true_and, paddingOnlyWord]
  constructor
  · rintro ⟨a, ⟨i, rfl⟩, hp⟩
    refine ⟨i, ?_⟩
    change p ∈ (q i * 1).primeFactors at hp
    simpa only [mul_one] using hp
  · rintro ⟨i, hp⟩
    refine ⟨⟨false, 1, q i⟩, ⟨i, rfl⟩, ?_⟩
    change p ∈ (q i * 1).primeFactors
    simpa only [mul_one] using hp

theorem padding_catalog_reciprocal_sum (R M : ℕ) (Q : Finset ℕ)
    (F : Finset (Fin R → ℕ)) (U : ℝ) (hU : 1 ≤ U)
    (hQ : primeHarmonicMass Q ≤ U)
    (hsq : ∀ q ∈ F, ∀ i, Squarefree (q i))
    (hpool : ∀ q ∈ F, ∀ i, (q i).primeFactors ⊆ Q)
    (hcount : ∀ q ∈ F, ∀ i, (q i).primeFactors.card ≤ M) :
    (∑ q ∈ F, ∏ p ∈ paddingPrimeSupport q, (p : ℝ)⁻¹) ≤
      (∑ n : Fin (R * M + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) * U ^ (R * M) := by
  have hc : ∀ v ∈ F.image paddingOnlyWord,
      Fintype.card (ActualPrimeSlot v) ≤ R * M := by
    intro v hv
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hv
    simpa only [zero_add] using actualPrimeSlot_card_le (paddingOnlyWord q) 0 M
      (by intro i; simp [paddingOnlyWord]) (hcount q hq)
  have hb := numerical_word_reciprocal_sum_le R (R * M) ∅ Q
    (F.image paddingOnlyWord) (fun _ => 1) 1 U (by norm_num) hU
    (by simpa [primeHarmonicMass] using zero_le_one.trans hU) hQ
    (by intros; exact le_rfl) hc
    (by intro v hv i; obtain ⟨q, _, rfl⟩ := mem_image.mp hv; simp [paddingOnlyWord])
    (by intro v hv i; obtain ⟨q, hq, rfl⟩ := mem_image.mp hv; exact hsq q hq i)
    (by intro v hv i; obtain ⟨q, _, rfl⟩ := mem_image.mp hv; simp [paddingOnlyWord])
    (by intro v hv i; obtain ⟨q, hq, rfl⟩ := mem_image.mp hv; exact hpool q hq i)
    (by intro v hv i j; obtain ⟨q, _, rfl⟩ := mem_image.mp hv; simp [paddingOnlyWord])
  rw [sum_image (fun q _ r _ he => paddingOnlyWord_injective R he)] at hb
  simpa only [one_mul, paddingOnlyWord_support] using hb

end TwoPointCorrelations

end OAI
