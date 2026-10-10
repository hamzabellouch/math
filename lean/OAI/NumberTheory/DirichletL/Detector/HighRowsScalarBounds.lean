import OAI.NumberTheory.DirichletL.Detector.HighRowsRegion

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma primeGauss_norm_le (p : O) (hp : p≠0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (h : O) :
    ‖primeGauss p hp χ h‖≤(Ideal.absNorm (Ideal.span {p}):ℝ) := by
  let := finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primeGauss,tsum_fintype]
  calc
    _ ≤ ∑ x : O ⧸ Ideal.span {p},‖χ x*quotientTrace p hp (Ideal.Quotient.mk _ h*x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : O ⧸ Ideal.span {p},(1:ℝ) := Finset.sum_le_sum fun x _=>by
      rw [norm_mul,(quotientTrace p hp).norm_apply,mul_one]
      exact QuadraticInitialBound.norm_finite_character_le_one χ x
    _ = _ := by simp [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

lemma primeGauss_actual_norm (p : O) (hp : p≠0) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2) :
    ‖primeGauss p hp (actualSextic (Ideal.span {p}) hg) 1‖=
      Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hn := localGamma_norm_one p hp hg hc 1 (by decide) (by decide)
  rw [localGamma,ProbePhase.normalizedTraceGauss_eq_normalizedGauss] at hn
  simp only [pow_one,ProbeGauss.normalizedGauss,norm_div,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hn
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp))
  have hcard : (Fintype.card (O ⧸ Ideal.span {p}):ℝ)=Ideal.absNorm (Ideal.span {p}) := by
    rw [←Nat.card_eq_fintype_card];rfl
  rw [hcard] at hn
  have hn' := (div_eq_one_iff_eq (Real.sqrt_pos.mpr hQ).ne').mp hn
  simpa only [primeGauss,tsum_fintype,gaussSum,map_one,one_mul] using hn'

lemma gaussValuationTable_norm_le (Q : ℝ) (hQ : 1≤Q) (G : ℂ) (hG : ‖G‖≤Q)
    (r n j : ℕ) : ‖gaussValuationTable (Q:ℂ) G r n j‖≤2*Q^(n+1) := by
  have hQ0 : 0≤Q := by linarith
  have hn : Q^n≤Q^(n+1) := by simpa only [pow_succ] using
    (le_mul_of_one_le_right (pow_nonneg hQ0 n) hQ)
  have hpow (a : ℕ) : ‖(Q:ℂ)^a‖=Q^a := by simp [norm_pow,abs_of_nonneg hQ0]
  have hi (a : ℕ) : ‖(if a≤j then (Q:ℂ)^a else 0)‖≤Q^a := by
    split_ifs
    · exact (hpow a).le
    · simpa only [norm_zero] using pow_nonneg hQ0 a
  unfold gaussValuationTable
  by_cases hr : 6∣r
  · rw [ite_eq_left hr]
    exact (norm_sub_le _ _).trans ((add_le_add (hi (n+1)) (hi n)).trans (by linarith))
  · rw [ite_eq_right hr]
    by_cases hj : j=n
    · rw [ite_eq_left hj,norm_mul,hpow]
      calc
        _ ≤ Q^n*Q := mul_le_mul_of_nonneg_left hG (pow_nonneg hQ0 n)
        _ ≤ 2*Q^(n+1) := by rw [←pow_succ];nlinarith [pow_nonneg hQ0 (n+1)]
    · rw [ite_eq_right hj,norm_zero]
      positivity

lemma positiveScalar_norm_le (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (n k j : ℕ) (hk : k≤1) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)*
        (Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ))^k := by
  have hP : Prime (Ideal.span {p}:Ideal O) := Ideal.prime_span_singleton_iff.mpr hp
  have hQ : (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    have hh := SmoothMobiusCorrection.prime_norm_two_le ⟨_,hP⟩
    change 2≤Ideal.absNorm (Ideal.span {p}) at hh
    exact_mod_cast (by omega : 1≤Ideal.absNorm (Ideal.span {p}))
  have ht (r j : ℕ) := gaussValuationTable_norm_le (Ideal.absNorm (Ideal.span {p}):ℝ) hQ
    (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^r) 1)
    (primeGauss_norm_le p hp.ne_zero _ _) r n j
  have ho : ‖actualSextic (Ideal.span {p}) hg (-1)‖=1 :=
    Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide)
  rw [positiveScalar_actual_table p hp hg hc]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
  · simpa only [ite_true,pow_zero,mul_one,Complex.ofReal_natCast] using ht (n+1) j
  · simp only [Nat.one_ne_zero,ite_false,true_and]
    split_ifs
    · rw [norm_mul,norm_mul,norm_inv,ho,inv_one,one_mul,primeGauss_actual_norm p hp.ne_zero hg hc]
      simpa only [pow_one,mul_comm,Complex.ofReal_natCast] using
        mul_le_mul_of_nonneg_left (ht n (j-1)) (Real.sqrt_nonneg (Ideal.absNorm (Ideal.span {p}):ℝ))
    · simp only [norm_zero,pow_one]
      positivity

end SevenEighths.ProbePrimePower
end

end OAI
