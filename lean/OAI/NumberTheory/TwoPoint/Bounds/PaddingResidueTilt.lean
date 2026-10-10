import OAI.NumberTheory.TwoPoint.Bounds.PaddingDivisorEncoding
import OAI.NumberTheory.TwoPoint.Bounds.PositiveWordProbability
import OAI.NumberTheory.TwoPoint.Bounds.CommonResidueLift
import OAI.NumberTheory.TwoPoint.Bounds.SieveModel

namespace OAI

/-! At every translated site of the uniform residue model, divisibility
indicators give independent Bernoulli(1/p) variables. Thus the exact weighted
residue expectation is the tilted padding law used in the bin-square bound. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def paddingResidueAvailable (Q : Finset ℕ) (B : ℕ)
    (n : ℤ) (z : Q → Fin B) (p : Q) : Bool :=
  decide ((p.val : ℤ) ∣ (z p).val + n)

lemma padding_residue_single_law (B p : ℕ) (hp : 2 ≤ p) (hpB : p ≤ B)
    (n : ℤ) (b : Bool) :
    (uniformResidueLaw B p (by omega) hpB).probability
      (fun z => decide ((p : ℤ) ∣ (z.val : ℤ) + n) = b) =
        (paddingOriginalPrimeLaw p hp).weight b := by
  have he (z : Fin B) : (p : ℤ) ∣ (z.val : ℤ) + n ↔
      (z.val : ZMod p) = -(n : ZMod p) :=
    residue_offset_divisibility (z.val : ZMod p) z.val n (by simp)
  have hh : (uniformResidueLaw B p (by omega) hpB).probability
      (fun z => (p : ℤ) ∣ (z.val : ℤ) + n) = (p : ℝ)⁻¹ := by
    simpa only [he] using uniformResidueLaw_mod_eq B p (by omega) hpB (-(n : ZMod p))
  cases b
  · have hc := FiniteLaw.probability_complement (uniformResidueLaw B p (by omega) hpB)
      (fun z => (p : ℤ) ∣ (z.val : ℤ) + n)
    rw [hh] at hc
    simpa [paddingOriginalPrimeLaw, booleanLaw, one_div] using hc
  · simpa [paddingOriginalPrimeLaw, booleanLaw, one_div] using hh

lemma padding_residue_average (Q : Finset ℕ) (B : ℕ)
    (hQ : ∀ p ∈ Q, 2 ≤ p) (hQB : ∀ p ∈ Q, p ≤ B) (n : ℤ)
    (F : (Q → Bool) → ℝ) :
    (FiniteLaw.independent (fun p : Q =>
      uniformResidueLaw B p.val (by have := hQ p p.property; omega) (hQB p p.property))).average
        (fun z => F (paddingResidueAvailable Q B n z)) =
          (paddingOriginalLaw Q hQ).average F := by
  exact FiniteLaw.independent_average_map
    (fun p : Q => uniformResidueLaw B p.val (by have := hQ p p.property; omega) (hQB p p.property))
    (fun p : Q => paddingOriginalPrimeLaw p (hQ p p.property))
    (fun p (z : Fin B) => decide ((p.val : ℤ) ∣ (z.val : ℤ) + n))
    (fun p b => padding_residue_single_law B p (hQ p p.property) (hQB p p.property) n b) F

lemma padding_residue_tilt (Q : Finset ℕ) (B : ℕ)
    (hQ : ∀ p ∈ Q, 2 ≤ p) (hQB : ∀ p ∈ Q, p ≤ B) (n : ℤ)
    (F : (Q → Bool) → ℝ) :
    (FiniteLaw.independent (fun p : Q =>
      uniformResidueLaw B p.val (by have := hQ p p.property; omega) (hQB p p.property))).average
        (fun z => paddingTiltWeight Q (paddingResidueAvailable Q B n z) *
          F (paddingResidueAvailable Q B n z)) /
            paddingTiltNormalizer Q = (paddingAvailableLaw Q hQ).average F := by
  rw [padding_residue_average Q B hQ hQB n (fun a => paddingTiltWeight Q a * F a),
    padding_tilt_average Q hQ F]
  exact mul_div_cancel_left₀ _ (paddingTiltNormalizer_pos Q).ne'

lemma padding_residue_bin_square_le (Q : Finset ℕ) (B : ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hQB : ∀ p ∈ Q, p ≤ B) (n : ℤ)
    (η c : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (bins : Finset ℤ) :
    (FiniteLaw.independent (fun p : Q =>
      uniformResidueLaw B p.val (hQ p p.property).pos (hQB p p.property))).average
        (fun z => paddingTiltWeight Q (paddingResidueAvailable Q B n z) *
          ∑ j ∈ bins, (literalPaddingBinMass Q (paddingResidueAvailable Q B n z) η c j) ^ 2) /
            paddingTiltNormalizer Q ≤
      (paddingDifferenceLaw Q (fun p hp => (hQ p hp).two_le)).probability
        (fun x => |paddingDifferenceValue Q x| ≤ 1) := by
  simp_rw [← paddingBinMass_eq_literal Q hQ]
  rw [padding_residue_tilt Q B (fun p hp => (hQ p hp).two_le) hQB n
    (fun a => ∑ j ∈ bins, (paddingBinMass Q a η c j) ^ 2)]
  exact padding_bin_square_small_ball Q _ η c hη hη1 bins

/-- Literal residue-model `rho_j`, weighted by `w/S`, satisfies the padding
anti-concentration estimate uniformly in site and bin translation. -/
theorem ModFiveThetaInput.padding_residue_bin_square (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L η c : ℝ) (B : ℕ) (n : ℤ) (bins : Finset ℤ),
      1 ≤ L → 0 < η → η ≤ 1 →
      ∀ hQB : ∀ p ∈ paddingPrimeSupply E L, p ≤ B,
      (FiniteLaw.independent (fun p : paddingPrimeSupply E L =>
        uniformResidueLaw B p.val (paddingPrimeSupply_prime p.property).pos
          (hQB p p.property))).average (fun z =>
            paddingTiltWeight _ (paddingResidueAvailable _ B n z) *
              ∑ j ∈ bins, (literalPaddingBinMass _ (paddingResidueAvailable _ B n z) η c j) ^ 2) /
                paddingTiltNormalizer (paddingPrimeSupply E L) ≤ C / L := by
  obtain ⟨C, hC, hbound⟩ := hP.padding_small_ball E
  refine ⟨C, hC, fun L η c B n bins hL hη hη1 hQB => ?_⟩
  exact (padding_residue_bin_square_le (paddingPrimeSupply E L) B
    (fun _ hp => paddingPrimeSupply_prime hp) hQB n η c hη hη1 bins).trans (hbound L hL)

end TwoPointCorrelations

end OAI
