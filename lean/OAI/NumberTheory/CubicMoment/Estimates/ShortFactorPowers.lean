import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorMoments

namespace OAI

/-! Absorbing the explicit logarithmic factors in the short-polynomial
moments, without making subpower growth an assumption. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma one_add_log_small_power {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 1 ≤ x → 1+Real.log x ≤ A*x^η := by
  refine ⟨1+1/η,by positivity,?_⟩
  intro x hx
  have hp := Real.one_le_rpow hx hη.le
  have hl := Real.log_le_rpow_div (zero_le_one.trans hx) hη
  calc
    _ ≤ x^η+x^η/η := add_le_add hp hl
    _ = _ := by ring

lemma shortFactorPolynomial_norm_le {F X : ℝ} {A : EisensteinArithmeticFunction}
    (hA : ShortArithmeticFactor F A) (hX : 1 ≤ X) (u : Eisenstein → ℂ)
    (hu : ∀ a ∈ primaryElementBall X, ‖u a‖ ≤ 1) :
    ‖primaryIdealPolynomial X A u‖ ≤ 18*X*(1+Real.log X) := by
  rw [primaryIdealPolynomial_eq_elements]
  calc
    _ ≤ ∑ a ∈ primaryElementBall X,
        ‖((MvPowerSeries.coeff (idealExponentOf a) A:ℝ):ℂ)*u a‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ primaryElementBall X, (1+Real.log X) :=
      Finset.sum_le_sum (fun a ha => shortArithmeticFactor_twisted_norm hA hX ha _ (hu a ha))
    _ = ((primaryElementBall X).card:ℝ)*(1+Real.log X) := by
      rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (primaryElementBall_card_le (by linarith))
      (by linarith [Real.log_nonneg hX])

theorem shortFactorPolynomial_norm_small_power {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F X : ℝ) (A : EisensteinArithmeticFunction),
      ShortArithmeticFactor F A → 1 ≤ X → ∀ u : Eisenstein → ℂ,
      (∀ a ∈ primaryElementBall X, ‖u a‖ ≤ 1) →
      ‖primaryIdealPolynomial X A u‖ ≤ C*X^(1+η) := by
  obtain ⟨C,hC,hbound⟩ := one_add_log_small_power hη
  refine ⟨18*C,by positivity,?_⟩
  intro F X A hA hX u hu
  apply (shortFactorPolynomial_norm_le hA hX u hu).trans
  calc
    _ ≤ 18*X*(C*X^η) := mul_le_mul_of_nonneg_left (hbound X hX) (by positivity)
    _ = (18*C)*X^(1+η) := by
      rw [Real.rpow_add (zero_lt_one.trans_le hX),Real.rpow_one]
      ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem logarithmic_factor_product (k : ι → ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ι → ℝ, (∀ i, 1 ≤ X i) →
      (∏ i, (1+Real.log (X i))^(k i)) ≤ C*(∏ i, (X i)^(k i))^η := by
  obtain ⟨A,hA,hbound⟩ := one_add_log_small_power hη
  refine ⟨∏ i, A^(k i),Finset.prod_pos (fun _ _ => pow_pos hA _),?_⟩
  intro X hX
  have hp (i : ι) : ((X i)^η)^(k i) = ((X i)^(k i))^η := by
    rw [← Real.rpow_mul_natCast (zero_le_one.trans (hX i)),
      ← Real.rpow_natCast_mul (zero_le_one.trans (hX i))]
    congr 1
    ring
  calc
    _ ≤ ∏ i, (A*(X i)^η)^(k i) := Finset.prod_le_prod₀
      (fun i _ => pow_nonneg (by linarith [Real.log_nonneg (hX i)]) _)
      (fun i _ => pow_le_pow_left₀ (by linarith [Real.log_nonneg (hX i)]) (hbound _ (hX i)) _)
    _ = (∏ i, A^(k i))*(∏ i, ((X i)^(k i))^η) := by
      simp_rw [mul_pow,hp]
      rw [Finset.prod_mul_distrib]
    _ = _ := by rw [Real.finsetProd_rpow _ _ (fun i _ => pow_nonneg (zero_le_one.trans (hX i)) _) η]

private lemma half_power_absorb {N L ε : ℝ} (hN : 1 ≤ N) (hL : 1 ≤ L)
    (hε : 0 ≤ ε) : (N*L)^(ε/2)*L^(ε/2) ≤ (N*L)^ε := by
  calc
    _ ≤ (N*L)^(ε/2)*(N*L)^(ε/2) := by
      gcongr
      exact le_mul_of_one_le_left (zero_le_one.trans hL) hN
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

/-- The exact short-factor cubic moments have the clean subpower-loss
form used to extract the limiting multiplicity inequalities. -/
theorem shortFactor_multiplicity_power (k : ι → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ),
      (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, ∀ a ∈ primaryElementBall (X i), ‖u i a‖ ≤ 1) →
      ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ N →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∑ a ∈ P, ‖∏ i,
        (primaryIdealPolynomial (X i) (A i) (fun n => u i n*cubicSymbol a n))^(k i)‖^2) ≤
        C*(N*(∏ i, (X i)^(k i)))^ε*(∏ i, (X i)^(k i))*
          (N+(∏ i, (X i)^(k i))+(N*(∏ i, (X i)^(k i)))^(2/3:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := shortFactor_multiplicity_moment k
    (show 0 < ε/2 by linarith) (show 0 < ε/4 by linarith)
  obtain ⟨B,hB,hlog⟩ := logarithmic_factor_product k (show 0 < ε/8 by linarith)
  refine ⟨C*B^2,by positivity,?_⟩
  intro F X A u hA hX hu P N hN hP
  let L : ℝ := ∏ i, (X i)^(k i)
  let G : ℝ := ∏ i, (1+Real.log (X i))^(k i)
  have hL : 1 ≤ L := Finset.one_le_prod₀ (fun i _ => one_le_pow₀ (hX i))
  have hG : 0 ≤ G := Finset.prod_nonneg
    (fun i _ => pow_nonneg (by linarith [Real.log_nonneg (hX i)]) _)
  have hpow : (L^(ε/8))^2 = L^(ε/4) := by
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hL)]
    congr 1
    ring
  have hG2 : G^2 ≤ B^2*L^(ε/4) := by
    have h := pow_le_pow_left₀ hG (hlog X hX) 2
    change G^2 ≤ (B*L^(ε/8))^2 at h
    simpa only [mul_pow,hpow] using h
  apply (hbound F X A u hA hX hu P N hN hP).trans
  change C*(N*L)^(ε/2)*L*(N+L+(N*L)^(2/3:ℝ))*(L^(ε/4)*G^2) ≤ _
  calc
    _ ≤ C*(N*L)^(ε/2)*L*(N+L+(N*L)^(2/3:ℝ))*(L^(ε/4)*(B^2*L^(ε/4))) := by
      gcongr
    _ = (C*B^2)*((N*L)^(ε/2)*L^(ε/2))*L*(N+L+(N*L)^(2/3:ℝ)) := by
      have hp : L^(ε/4)*L^(ε/4) = L^(ε/2) := by
        rw [← Real.rpow_add (zero_lt_one.trans_le hL)]
        congr 1
        ring
      calc
        _ = (C*B^2)*((N*L)^(ε/2)*(L^(ε/4)*L^(ε/4)))*L*(N+L+(N*L)^(2/3:ℝ)) := by ring
        _ = _ := by rw [hp]
    _ ≤ (C*B^2)*(N*L)^ε*L*(N+L+(N*L)^(2/3:ℝ)) := by
      gcongr
      exact half_power_absorb hN hL hε.le

 /-- The ordinary mixed moments have the same fully absorbed loss. -/
theorem shortFactor_mixed_multiplicity_power
    (hHuxley : HuxleyAdditiveLargeSieve) (k : ι → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ),
      (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, ∀ a ∈ primaryElementBall (X i), ‖u i a‖ ≤ 1) →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (Q : ℝ), 1 ≤ Q →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∑ p ∈ P, ‖∏ i, (primaryIdealPolynomial (X i) (A i)
        (fun n => u i n*mixedCubic p.1 p.2 n))^(k i)‖^2) ≤
        C*(Q*(∏ i, (X i)^(k i)))^ε*(∏ i, (X i)^(k i))*
          (Q^2+(∏ i, (X i)^(k i))) := by
  obtain ⟨C,hC,hbound⟩ := shortFactor_mixed_multiplicity_moment hHuxley k hε
    (show 0 < ε/2 by linarith)
  obtain ⟨B,hB,hlog⟩ := logarithmic_factor_product k (show 0 < ε/4 by linarith)
  let T : ℝ := ∏ i, (18:ℝ)^(k i)
  have hT : 0 < T := Finset.prod_pos (fun _ _ => by positivity)
  refine ⟨C*T*B^2,by positivity,?_⟩
  intro F X A u hA hX hu P Q hQ hP
  let L : ℝ := ∏ i, (X i)^(k i)
  let G : ℝ := ∏ i, (1+Real.log (X i))^(k i)
  have hL : 1 ≤ L := Finset.one_le_prod₀ (fun i _ => one_le_pow₀ (hX i))
  have hG : 0 ≤ G := Finset.prod_nonneg
    (fun i _ => pow_nonneg (by linarith [Real.log_nonneg (hX i)]) _)
  have hpow : (L^(ε/4))^2 = L^(ε/2) := by
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hL)]
    congr 1
    ring
  have hG2 : G^2 ≤ B^2*L^(ε/2) := by
    have h := pow_le_pow_left₀ hG (hlog X hX) 2
    change G^2 ≤ (B*L^(ε/4))^2 at h
    simpa only [mul_pow,hpow] using h
  have hE : (∏ i, (18*X i*(1+Real.log (X i))^2)^(k i)) = T*L*G^2 := by
    calc
      _ = ∏ i, (18:ℝ)^(k i)*(X i)^(k i)*((1+Real.log (X i))^(k i))^2 := by
        apply Finset.prod_congr rfl
        intro i _
        rw [mul_pow,mul_pow,pow_right_comm]
      _ = _ := by
        rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,Finset.prod_pow]
  apply (hbound F X A u hA hX hu P Q hQ hP).trans
  rw [hE]
  change C*Q^ε*(Q^2+L)*(L^(ε/2)*(T*L*G^2)) ≤ _
  calc
    _ ≤ C*Q^ε*(Q^2+L)*(L^(ε/2)*(T*L*(B^2*L^(ε/2)))) := by gcongr
    _ = (C*T*B^2)*(Q*L)^ε*L*(Q^2+L) := by
      have hp : L^(ε/2)*L^(ε/2) = L^ε := by
        rw [← Real.rpow_add (zero_lt_one.trans_le hL)]
        congr 1
        ring
      rw [Real.mul_rpow (zero_le_one.trans hQ) (zero_le_one.trans hL)]
      calc
        _ = (C*T*B^2)*Q^ε*(L^(ε/2)*L^(ε/2))*L*(Q^2+L) := by ring
        _ = _ := by rw [hp]; ring

end CubicFirstMoment

end

end OAI
