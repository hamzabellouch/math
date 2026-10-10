import OAI.NumberTheory.JointDickman.Arithmetic.PrimeBandExtractionCost

namespace OAI

/-! # A summed bound for every nonexceptional frequency class -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations

lemma canonical_initialCost_nonneg (P Q η : ℝ) (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ (canonicalMellinBands P Q η).initialCost N T := by
  unfold MellinPrimeBands.initialCost canonicalMellinBands mrtPrimeLogLower
  positivity

theorem canonical_small_cost_sum_le {P Q η : ℝ} (J N : ℕ) (hJ : 0 < J) {T : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1/12) (hP0 : 0 < P) (hP : 2 ≤ Real.log P)
    (hQ : 1 ≤ Real.log Q) (hPQ : P ≤ Q)
    (hbudget : 8192 * (Real.log (Real.log Q) + 1) ≤ η * Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η) (hN : 0 < (N : ℝ)) (hT : 0 ≤ T) :
    (∑ j ∈ range J, if j = 0 then (canonicalMellinBands P Q η).initialCost N T
      else (canonicalMellinBands P Q η).laterCost j N T) ≤
      1024 * Real.exp 2 * (T*Q/N+1) * (mrtBaseResolution P Q η)⁻¹ +
        2*(T/N+1)/P := by
  let D := canonicalMellinBands P Q η
  let C : ℝ := (T/N+1)*P⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hterm (j : ℕ) : (if j = 0 then D.initialCost N T else D.laterCost j N T) ≤
      (if j = 0 then D.initialCost N T else 0) + C * (((j+1 : ℕ) : ℝ)^2)⁻¹ := by
    by_cases hj : j = 0
    · simp only [hj, ite_true]
      exact le_add_of_nonneg_right (mul_nonneg hC (by positivity))
    · simp only [hj, ite_false, zero_add]
      have hh := canonical_laterCost_le (j-1) N hη (by linarith) hP0 hP hQ
        (Real.log_le_log hP0 hPQ) hbudget hH hT
      have hn : j-1+1 = j := by omega
      have he : ((j-1 : ℕ) : ℝ)+2 = (j+1 : ℕ) := by
        have hh : j-1+2 = j+1 := by omega
        exact_mod_cast hh
      simpa only [hn, he, C, D] using hh
  have hP1 : 1 ≤ P := by
    have hh := Real.exp_le_exp.mpr hP
    rw [Real.exp_log hP0] at hh
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hmain := canonical_initialCost_le N hη.le hη' hP1 (hP0.trans_le hPQ)
    hQ hH hN hT
  calc
    _ ≤ ∑ j ∈ range J, ((if j = 0 then D.initialCost N T else 0) +
        C * (((j+1 : ℕ) : ℝ)^2)⁻¹) := sum_le_sum (fun j _ => hterm j)
    _ = D.initialCost N T + C * ∑ j ∈ range J, (((j+1 : ℕ) : ℝ)^2)⁻¹ := by
      rw [sum_add_distrib, ← mul_sum]
      simp only [sum_ite_eq', mem_range, hJ, ite_true]
    _ ≤ D.initialCost N T + C * 2 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_range_succ_inv_sq_le J) hC)
    _ ≤ _ := by
      change D.initialCost N T ≤ _ at hmain
      dsimp only [C]
      linarith [show (T/N+1)*P⁻¹*2 = 2*(T/N+1)/P by ring]

/-- This is the actual Dirichlet energy estimate away from the residual
class: all selected-band costs have been summed, independently of their
number. The no-small-band integral is retained verbatim. -/
theorem canonical_mellin_energy_bound {P Q η : ℝ} {J N : ℕ} (hJ : 0 < J)
    (hPbig : 2*Real.exp 1 ≤ P) (hP : 2 ≤ Real.log P) (hPQ : P ≤ Q)
    (hη : 0 < η) (hη' : η ≤ 1/12)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η) (hN : 0 < N)
    (hupper : ∀ j ∈ range J, 2*mrtBandUpper Q (j+1) ≤ N)
    (f : ℕ → ℂ) (hf : Multiplicative f) (hb : OneBounded f)
    {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ Set.Ioc (-T) T) :
    (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N))
      (mrtTypicalCoefficient (range J) (canonicalMellinBands P Q η).primes f) t‖^2) ≤
    (∫ t in S ∩ mrtNoSmallBand (canonicalMellinBands P Q η).bins
        ((canonicalMellinBands P Q η).polynomial f) (canonicalMellinBands P Q η).threshold J,
      ‖angularMellinPolynomial (Ioc N (2*N))
        (mrtTypicalCoefficient (range J) (canonicalMellinBands P Q η).primes f) t‖^2) +
    2816*Real.exp 1*(T/N+1)*(8/P+4/(mrtBaseResolution P Q η)) +
    1024*Real.exp 2*(T*Q/N+1)*(mrtBaseResolution P Q η)⁻¹ + 2*(T/N+1)/P := by
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hPbig
  have hQ : 1 ≤ Real.log Q :=
    (show 1 ≤ Real.log P by linarith).trans (Real.log_le_log hP0 hPQ)
  have hd := canonicalMellinBands_valid hPbig hPQ (by linarith) hH hupper
  have hh := (canonicalMellinBands P Q η).partition_energy_le hd hN f hf hb hT hSm hS
  rw [sum_add_distrib] at hh
  have he := canonical_extraction_sum_le (η := η) J N hP0 hP hQ hPQ hH hT.le
  have hc := canonical_small_cost_sum_le J N hJ hη hη' hP0 hP hQ hPQ hbudget hH
    (by exact_mod_cast hN) hT.le
  linarith

end JointDickman

end OAI
