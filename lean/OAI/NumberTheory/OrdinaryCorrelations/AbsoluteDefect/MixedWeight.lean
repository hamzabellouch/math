import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BadFrequencies

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryTwoScaleCofactor
open Finset OrdinaryDirichletMeanSquare OrdinaryPrimeDirichletMoments
open OrdinaryDirichletFiberMoments SourcePrimeFactor OrdinaryRestrictedCofactor

def mixedWeight (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (A P : Finset ℕ) {k : ℕ} (z : (Fin k → A) × ℕ) : ℂ :=
  tupleCoefficient (fun p => characterModulation f χ p/(p:ℂ)) z.1 *
    OrdinaryCofactorDyadicBound.coefficient P (characterModulation f χ) z.2

def mixedCoefficient (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (A P : Finset ℕ) (k M n : ℕ) : ℂ :=
  collect (powersAndCofactors A k M) productLocation (mixedWeight f χ A P) n

def mixedEnergy (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (A P : Finset ℕ) (k M : ℕ) : ℝ :=
  ∑ n ∈ (powersAndCofactors A k M).image productLocation,
    ‖mixedCoefficient f χ A P k M n‖^2

lemma mixedEnergy_nonneg (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (A P : Finset ℕ) (k M : ℕ) : 0 ≤ mixedEnergy f χ A P k M :=
  sum_nonneg fun _ _ => sq_nonneg _

lemma actual_two_scale_polynomial (f : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (A P : Finset ℕ) (hA : ∀p∈A,Nat.Prime p)
    (k M : ℕ) (t : ℝ) :
    polynomial ((powersAndCofactors A k M).image productLocation)
      (mixedCoefficient f χ A P k M) (fun n => Real.log n) t =
      primeMellin f χ A t ^ k * dyadicCofactorMellin f χ P M t := by
  unfold mixedCoefficient
  rw [collect_polynomial, primeMellin_pow_expansion f χ A hA,
    dyadicCofactorMellin_eq_polynomial]
  unfold powersAndCofactors polynomial
  rw [sum_product, sum_mul]
  apply sum_congr rfl
  intro v hv
  rw [mul_sum]
  apply sum_congr rfl
  intro m hm
  have hm0 : 0 < m := by have := (mem_Ioc.mp hm).1; omega
  rw [productLocation, OrdinaryRestrictedCofactor.phase_log_mul (tupleProduct_pos hA v) hm0]
  unfold mixedWeight
  ring

theorem mixed_spaced_energy (f : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (A P : Finset ℕ) (hA : ∀p∈A,Nat.Prime p)
    (k : ℕ) {M : ℕ} (hM : 0 < M) (R : Finset ℝ) {Q T c B : ℝ}
    (hQ : 0 < Q) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hAQ : ∀p∈A,(p:ℝ)≤Q) (hband : ∀p∈A, |Real.log (p:ℝ)-c|≤B)
    (hR : ∀t∈R,t∈Set.Icc (-T) T)
    (hsep : ∀t∈R,∀u∈R,t≠u → 1≤|t-u|) :
    ∑ t ∈ R, ‖primeMellin f χ A t‖^(2*k) * ‖dyadicCofactorMellin f χ P M t‖^2 ≤
      4*Real.exp (1+1/4)*gaussianConstant*(T+1+Q^k*(2*M:ℝ))*
        (2+((k:ℝ)*B+Real.log 2)^2)*mixedEnergy f χ A P k M := by
  have he (t : ℝ) :
      ‖polynomial ((powersAndCofactors A k M).image productLocation)
        (mixedCoefficient f χ A P k M) (fun n => Real.log n) t‖^2 =
        ‖primeMellin f χ A t‖^(2*k) * ‖dyadicCofactorMellin f χ P M t‖^2 := by
    rw [actual_two_scale_polynomial f χ A P hA, norm_mul, mul_pow, norm_pow, ← pow_mul]
    congr 2
    omega
  simp_rw [← he]
  apply OrdinaryMellinSampling.band_spaced_mean_square _ _ R
    (mul_pos (pow_pos hQ k) (by exact_mod_cast (show 0<2*M by omega))) hT
    (add_nonneg (mul_nonneg (Nat.cast_nonneg k) hB) (Real.log_nonneg (by norm_num)))
    (actual_support_bounds A hA k M hQ hAQ)
    (actual_support_band A hA k hM hband) hR hsep

def transitionFrequencies (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (A P : Finset ℕ) (R : Finset ℝ) (V W : ℝ) : Finset ℝ := by
  classical
  exact R.filter (fun t => V < ‖primeMellin f χ A t‖ ∧ ‖primeMellin f χ P t‖ ≤ W)

def transitionEnergy (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (A P : Finset ℕ) (M : ℕ) (R : Finset ℝ) (V W : ℝ) : ℝ :=
  ∑ t ∈ transitionFrequencies f χ A P R V W,
    ‖primeMellin f χ P t‖^2 * ‖dyadicCofactorMellin f χ P M t‖^2

lemma transition_amplification (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (A P : Finset ℕ) (k M : ℕ) (R : Finset ℝ) {V W : ℝ} (hV : 0<V) (hW : 0≤W) :
    transitionEnergy f χ A P M R V W ≤
      (W^2 / V^(2*k)) * (∑ t ∈ R,
        ‖primeMellin f χ A t‖^(2*k) * ‖dyadicCofactorMellin f χ P M t‖^2) := by
  classical
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hV _)).mpr
  unfold transitionEnergy
  rw [sum_mul, mul_sum]
  calc
    _ ≤ ∑ t ∈ transitionFrequencies f χ A P R V W,
        W^2 * (‖primeMellin f χ A t‖^(2*k) * ‖dyadicCofactorMellin f χ P M t‖^2) := by
      apply sum_le_sum
      intro t ht
      have ht' := (mem_filter.mp ht).2
      have h1 := pow_le_pow_left₀ hV.le ht'.1.le (2*k)
      have h2 := pow_le_pow_left₀ (norm_nonneg _) ht'.2 2
      have h3 := mul_le_mul h2 h1 (pow_nonneg hV.le _) (pow_nonneg hW 2)
      have h4 := mul_le_mul_of_nonneg_right h3
        (sq_nonneg ‖dyadicCofactorMellin f χ P M t‖)
      nlinarith only [h4]
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro t ht hnot
      positivity

theorem actual_transition_energy (f : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (A P : Finset ℕ) (hA : ∀p∈A,Nat.Prime p)
    (k : ℕ) {M : ℕ} (hM : 0 < M) (R : Finset ℝ) {Q T c B V W : ℝ}
    (hQ : 0 < Q) (hT : 0 ≤ T) (hB : 0 ≤ B) (hV : 0 < V) (hW : 0 ≤ W)
    (hAQ : ∀p∈A,(p:ℝ)≤Q) (hband : ∀p∈A, |Real.log (p:ℝ)-c|≤B)
    (hR : ∀t∈R,t∈Set.Icc (-T) T)
    (hsep : ∀t∈R,∀u∈R,t≠u → 1≤|t-u|) :
    transitionEnergy f χ A P M R V W ≤
      (W^2 / V^(2*k)) *
      (4*Real.exp (1+1/4)*gaussianConstant*(T+1+Q^k*(2*M:ℝ))*
        (2+((k:ℝ)*B+Real.log 2)^2)*mixedEnergy f χ A P k M) := by
  exact (transition_amplification f χ A P k M R hV hW).trans
    (mul_le_mul_of_nonneg_left
      (mixed_spaced_energy f χ A P hA k hM R hQ hT hB hAQ hband hR hsep)
      (div_nonneg (sq_nonneg _) (pow_nonneg hV.le _)))

end OrdinaryTwoScaleCofactor

end

end OAI
