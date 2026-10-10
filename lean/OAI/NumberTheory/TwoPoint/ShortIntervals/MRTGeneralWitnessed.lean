import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeneralTypical
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWitnessedEnergy

namespace OAI

/-! Witnessed multiscale energy for ordinary multiplicative functions.
The complete-multiplicativity restriction has been removed using the
actual prime-square-supported extraction error. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_general_typical_witnessed_energy {ι κ β : Type*} [DecidableEq κ]
    (J : Finset ι) (P : ι → Finset ℕ)
    (hP : ∀ j ∈ J, ∀ p ∈ P j, p.Prime)
    (hdis : Set.PairwiseDisjoint (J : Set ι) P) {j : ι} (hj : j ∈ J)
    (K : Finset κ) (bin : ℕ → κ) (hbin : ∀ p ∈ P j, bin p ∈ K)
    (lower : κ → ℝ) {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 1 ≤ δ) (hδ2 : δ ≤ 2)
    (hL : ∀ p ∈ P j, lower (bin p) ≤ p ∧ (p : ℝ) ≤ δ * lower (bin p))
    (hlow : ∀ k ∈ K, 1 ≤ lower k)
    (F : ℕ → ℂ)
    (hF : Multiplicative F)
    (hFb : OneBounded F)
    (B : Finset β) (Pprev : β → Finset ℕ) (Y : β → ℝ)
    (hY : ∀ b ∈ B, 1 < Y b)
    (hprev : ∀ b ∈ B, ∀ p ∈ Pprev b, p.Prime)
    (hprevbin : ∀ b ∈ B, ∀ p ∈ Pprev b, Y b ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y b)
    (V : β → ℝ) (hV : ∀ b ∈ B, 0 < V b)
    {T : ℝ} (hT : 0 < T) {E : Set ℝ} (hE : MeasurableSet E)
    (hET : E ⊆ Set.Ioc (-T) T) (A : κ → ℝ)
    (hsmall : ∀ k ∈ K, ∀ t ∈ E,
      ‖mrtExponentialPolynomial ((P j).filter (fun p => bin p = k))
        (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t‖ ≤ A k)
    (hcover : ∀ t ∈ E, ∃ b ∈ B, V b ≤
      ‖mrtExponentialPolynomial (Pprev b) (fun p => F p / (p : ℂ))
        (fun p => -Real.log (p : ℝ)) t‖) :
    (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t‖ ^ 2) ≤
      2816 * Real.exp 1 * (T / (N : ℝ) + 1) *
        ((∑ p ∈ P j, 1 / (p : ℝ) ^ 2) +
          (∑ p ∈ P j, 1 / (p : ℝ) ^ 2) ^ 2 + (δ - 1)) +
      2 * ∑ b ∈ B, (K.card : ℝ) * ∑ k ∈ K, (A k) ^ 2 *
        ((16 * Real.exp 10 *
          (T / (N : ℝ) + (2 : ℝ) ^ (mrtAmplificationOrder ⌈Y b⌉₊ (lower k) + 1) * ⌈Y b⌉₊) *
            ((mrtAmplificationOrder ⌈Y b⌉₊ (lower k)).factorial : ℝ) ^ 2) /
          (V b) ^ (2 * mrtAmplificationOrder ⌈Y b⌉₊ (lower k))) := by
  let C := mrtTypicalCoefficient (J.erase j) P F
  let Q : κ → ℝ → ℂ := fun k =>
    mrtExponentialPolynomial ((P j).filter (fun p => bin p = k))
      (fun p => F p / (p : ℂ)) (fun p => -Real.log (p : ℝ))
  let G : ℝ → ℂ := fun t => ∑ k ∈ K, Q k t * mrtCofactorPolynomial (P j) C N (lower k) t
  let D := mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N
  have hG : Continuous G := continuous_finsetSum K (fun k _ =>
    (mrtExponentialPolynomial_continuous _ _ _).mul
      (mrtCofactorPolynomial_continuous (P j) C N (lower k)))
  have hc := mrt_witnessed_cofactor_energy K Q A lower (P j) C
    (mrtTypicalCoefficient_oneBounded _ _ _ hFb) hN hlow B Pprev Y hY hprev hprevbin
    (fun _ => F) (fun b hb p hp => hFb p (hprev b hb p hp).pos) V hV hT hE hET
    (fun _ _ => mrtExponentialPolynomial_continuous _ _ _) hsmall hcover
  change (∫ t in E, ‖G t‖ ^ 2) ≤ _ at hc
  have herr := mrt_typical_general_prime_mean_square J P hP hdis hj
    (fun p => lower (bin p)) hN hδ hδ2 hL F hF hFb hT
  simp_rw [mrt_extracted_prime_bins K (P j) bin hbin lower N F
    (mrtTypicalCoefficient (J.erase j) P F)] at herr
  change (∫ t in -T..T, ‖D t - G t‖ ^ 2) ≤ _ at herr
  apply (mrt_restricted_energy_split D G
    (mrtExponentialPolynomial_continuous _ _ _) hG hT.le hET).trans
  have hh := add_le_add (mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))
  convert hh using 1; ring

end TwoPointCorrelations

end OAI
