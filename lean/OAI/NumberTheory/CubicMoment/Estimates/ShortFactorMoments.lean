import OAI.NumberTheory.CubicMoment.Estimates.PrimaryMultiplicity

namespace OAI

/-! The actual short Möbius, zeta and logarithmic factors occurring in
the finite ideal convolution identity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def ShortArithmeticFactor (F : ℝ) (A : EisensteinArithmeticFunction) : Prop :=
  A = shortIdealMoebius F ∨ A = idealZeta ∨ A = idealLogNorm

lemma shortArithmeticFactor_norm {F X : ℝ} {A : EisensteinArithmeticFunction}
    (hA : ShortArithmeticFactor F A) (hX : 1 ≤ X) {a : Eisenstein}
    (ha : a ∈ primaryElementBall X) :
    ‖((MvPowerSeries.coeff (idealExponentOf a) A : ℝ) : ℂ)‖ ≤ 1+Real.log X := by
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  obtain ⟨ha,hNa⟩ := mem_primaryElementBall.mp ha
  rcases hA with rfl | rfl | rfl
  · rw [Complex.norm_real,Real.norm_eq_abs]
    exact (shortIdealMoebius_abs_le_one F _).trans (by linarith)
  · simp only [MvPowerSeries.coeff_apply,idealZeta,Complex.ofReal_one,norm_one]
    linarith
  · rw [MvPowerSeries.coeff_apply,idealLogNorm,idealExponentOf_norm (primary_ne_zero ha),
      Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (one_le_norm (primary_ne_zero ha)))]
    have h := Real.log_le_log (norm_pos_of_ne_zero (primary_ne_zero ha)) hNa
    linarith

lemma shortArithmeticFactor_twisted_norm {F X : ℝ} {A : EisensteinArithmeticFunction}
    (hA : ShortArithmeticFactor F A) (hX : 1 ≤ X) {a : Eisenstein}
    (ha : a ∈ primaryElementBall X) (u : ℂ) (hu : ‖u‖ ≤ 1) :
    ‖((MvPowerSeries.coeff (idealExponentOf a) A : ℝ) : ℂ)*u‖ ≤ 1+Real.log X := by
  rw [norm_mul]
  exact (mul_le_of_le_one_right (_root_.norm_nonneg _) hu).trans
    (shortArithmeticFactor_norm hA hX ha)

lemma primaryElementBall_card_le {X : ℝ} (hX : 0 ≤ X) :
    ((primaryElementBall X).card : ℝ) ≤ 18*X :=
  (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (nonzeroNormBall_card_le hX)

lemma shortArithmeticFactor_energy {F X : ℝ} {A : EisensteinArithmeticFunction}
    (hA : ShortArithmeticFactor F A) (hX : 1 ≤ X) (u : Eisenstein → ℂ)
    (hu : ∀ a ∈ primaryElementBall X, ‖u a‖ ≤ 1) :
    (∑ a ∈ primaryElementBall X,
      ‖((MvPowerSeries.coeff (idealExponentOf a) A : ℝ) : ℂ)*u a‖^2) ≤
      18*X*(1+Real.log X)^2 := by
  calc
    _ ≤ ∑ _a ∈ primaryElementBall X, (1+Real.log X)^2 :=
      Finset.sum_le_sum (fun a ha => pow_le_pow_left₀ (_root_.norm_nonneg _)
        (shortArithmeticFactor_twisted_norm hA hX ha (u a) (hu a ha)) 2)
    _ = ((primaryElementBall X).card:ℝ)*(1+Real.log X)^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (primaryElementBall_card_le (by linarith))
      (sq_nonneg _)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The fixed-multiplicity sharp cubic moment for the exact ideal
polynomials supplied by the short Möbius identity. -/
theorem shortFactor_multiplicity_moment (k : ι → ℕ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ),
      (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, ∀ a ∈ primaryElementBall (X i), ‖u i a‖ ≤ 1) →
      ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ N →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∑ a ∈ P, ‖∏ i,
        (primaryIdealPolynomial (X i) (A i) (fun n => u i n*cubicSymbol a n))^(k i)‖^2) ≤
        C*(N*(∏ i, (X i)^(k i)))^ε*(∏ i, (X i)^(k i))*
          (N+(∏ i, (X i)^(k i))+(N*(∏ i, (X i)^(k i)))^(2/3:ℝ))*
          ((∏ i, (X i)^(k i))^δ*(∏ i, (1+Real.log (X i))^(k i))^2) := by
  obtain ⟨C,hC,hbound⟩ := primaryPolynomial_multiplicity_moment k hε hδ
  refine ⟨C,hC,?_⟩
  intro F X A u hA hX hu P N hN hP
  have h := hbound (fun i => primaryElementBall (X i))
    (fun i a => ((MvPowerSeries.coeff (idealExponentOf a) (A i):ℝ):ℂ)*u i a)
    (fun i => 1+Real.log (X i)) X
    (fun _ _ ha => (mem_primaryElementBall.mp ha).1)
    (fun i => by linarith [Real.log_nonneg (hX i)])
    (fun i a ha => shortArithmeticFactor_twisted_norm (hA i) (hX i) ha _ (hu i a ha))
    hX (fun _ _ ha => (mem_primaryElementBall.mp ha).2) P N hN hP
  simpa only [primaryIdealPolynomial_eq_elements,mul_assoc] using h

/-- Actual short-factor mixed moments, with all individual coefficient
energies bounded explicitly. Huxley's additive sieve is the sole input. -/
theorem shortFactor_mixed_multiplicity_moment
    (hHuxley : HuxleyAdditiveLargeSieve) (k : ι → ℕ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ),
      (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, ∀ a ∈ primaryElementBall (X i), ‖u i a‖ ≤ 1) →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (Q : ℝ), 1 ≤ Q →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∑ p ∈ P, ‖∏ i, (primaryIdealPolynomial (X i) (A i)
        (fun n => u i n*mixedCubic p.1 p.2 n))^(k i)‖^2) ≤
        C*Q^ε*(Q^2+(∏ i, (X i)^(k i)))*
          ((∏ i, (X i)^(k i))^δ*(∏ i, (18*X i*(1+Real.log (X i))^2)^(k i))) := by
  obtain ⟨C,hC,hbound⟩ := primaryPolynomial_mixed_multiplicity_moment hHuxley k hε hδ
  refine ⟨C,hC,?_⟩
  intro F X A u hA hX hu P Q hQ hP
  let w : ι → Eisenstein → ℂ := fun i a =>
    ((MvPowerSeries.coeff (idealExponentOf a) (A i):ℝ):ℂ)*u i a
  have h := hbound (fun i => primaryElementBall (X i)) w X
    (fun _ _ ha => (mem_primaryElementBall.mp ha).1)
    hX (fun _ _ ha => (mem_primaryElementBall.mp ha).2) P Q hQ hP
  have henergy : (∏ i, (∑ n ∈ primaryElementBall (X i), ‖w i n‖^2)^(k i)) ≤
      ∏ i, (18*X i*(1+Real.log (X i))^2)^(k i) := by
    apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
    intro i _
    exact pow_le_pow_left₀ (by positivity)
      (shortArithmeticFactor_energy (hA i) (hX i) (u i) (hu i)) _
  have hL : 0 ≤ ∏ i, (X i)^(k i) :=
    Finset.prod_nonneg (fun i _ => pow_nonneg (zero_le_one.trans (hX i)) _)
  have hLδ : 0 ≤ (∏ i, (X i)^(k i))^δ := Real.rpow_nonneg hL _
  have h' := h.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left henergy (by positivity)) (by positivity))
  simpa only [primaryIdealPolynomial_eq_elements,w,mul_assoc] using h'

end CubicFirstMoment

end

end OAI
