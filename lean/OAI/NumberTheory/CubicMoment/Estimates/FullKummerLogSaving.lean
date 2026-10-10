import OAI.NumberTheory.CubicMoment.Estimates.KummerPrimeFactorization
import OAI.NumberTheory.CubicMoment.Estimates.ExcludedKummerLogSaving
import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeErrorSaving
import OAI.NumberTheory.CubicMoment.Estimates.IndependentPrimeSaving

namespace OAI

/-! Low-height saving for the full squarefree convolution with arbitrary
noncube numerator, including its ramified and unit parts. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem full_kummer_log_saving
    (hSW : KummerPrimeSiegelWalfisz) {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    {c d R A : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hR : 1 ≤ R) (hA : 0 < A)
    (k U : ℕ) (hk : 0 < k) :
    ∃ K Y₀ L₀ : ℝ, 0 < K ∧ 1 < Y₀ ∧ ∀ (r : γ) (X : ι → ℝ),
      (∀ i, Y₀ ≤ X i) → L₀ ≤ L r → 1 ≤ Real.log (L r) →
      (∏ i, X i) = L r → (∀ i, (L r)^c ≤ X i) →
      ∀ v : Eisenstein, v ≠ 0 → (¬∃ j : Eisenstein, j^3 = v) →
      (∀ i, norm v ≤ (Real.log (X i))^A) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ (L r)^d → ∀ u : ℝ,
      |u| ≤ (1+Real.log (L r))^U →
      ‖fullStructuredPrimeSum R v 1 1 e u (W r) X‖ ≤
        K*L r/(1+Real.log (L r))^k := by
  obtain ⟨K,Y₀,L₁,hK,hY₀,hprime⟩ := excluded_kummer_logarithmic_prime_saving hSW hW
    (fun z => hlo z.1 z.2) hc hd hR hA k U hk
  obtain ⟨L₂,herr⟩ := full_prime_error_log_saving hW hlo hc hR k
  refine ⟨K^(Fintype.card ι)+1,Y₀,max L₁ L₂,by positivity,hY₀,?_⟩
  intro r X hX hL hlog hlen hrough v hv hn hcon e he heL u hu
  have hLone : 1 ≤ L r := hW.length_one (r,Classical.arbitrary ι)
  have hXone : ∀ i, 1 ≤ X i := fun i => hY₀.le.trans (hX i)
  have hb : ‖∏ i, excludedSmoothPrimeCharacterSum R (X i) (W r i)
      (fun p => cubicSymbol p v) e u‖ ≤ K^(Fintype.card ι)*L r/(1+Real.log (L r))^k := by
    apply prime_product_log_bound _ X hK.le (fun i => zero_le_one.trans (hXone i)) hlen (by linarith) k
    intro i
    exact hprime (r,i) (X i) (hX i) ((le_max_left _ _).trans hL) hlog (hrough i)
      v hv hn (hcon i) e he heL u hu
  have hχ : ∀ b ∈ orderedConvolutionSupport (fullPrimeSupport R (W r) X),
      ‖cubicNumeratorHom v b‖ ≤ 1 := by
    intro b hb
    have hbp := orderedPrimarySupport_primary (fullPrimeSupport R (W r) X)
      (fun i p hp => (fullPrimeSupport_prime R (W r) X i p hp).1) hb
    rw [cubicNumeratorHom_primary v hbp]
    exact norm_cubicSymbol_le_one hbp v
  have he' := herr r X ((le_max_right _ _).trans hL) hLone hXone hlen hrough
    e (cubicNumeratorHom v) hχ 0 u 0
  have hid := fullStructuredPrimeSum_numerator_factorization R (W r) X v e u
  calc
    _ = ‖(∏ i, excludedSmoothPrimeCharacterSum R (X i) (W r i) (fun p => cubicSymbol p v) e u)-
        twistedErrorPrimePolynomial (fullPrimeSupport R (W r) X)
          (excludedPrimeWeight e (W r) X) (cubicNumeratorHom v) 0 u 0‖ := by
      rw [← hid]
      congr 1
      ring
    _ ≤ ‖∏ i, excludedSmoothPrimeCharacterSum R (X i) (W r i) (fun p => cubicSymbol p v) e u‖+
        ‖twistedErrorPrimePolynomial (fullPrimeSupport R (W r) X)
          (excludedPrimeWeight e (W r) X) (cubicNumeratorHom v) 0 u 0‖ := norm_sub_le _ _
    _ ≤ K^(Fintype.card ι)*L r/(1+Real.log (L r))^k+L r/(1+Real.log (L r))^k := add_le_add hb he'
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
