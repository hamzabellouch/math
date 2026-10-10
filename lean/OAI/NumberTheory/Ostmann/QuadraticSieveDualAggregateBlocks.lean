import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateWeighted

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate

theorem dual_range_energy_bootstrap {M N B x d₁ d₂ Q₁ Q₂ R κ F Z E : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hB : 0 < B) (hx : 0 ≤ x)
    (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (hR : 0 ≤ R) (hκ : 0 ≤ κ)
    (hF : 0 ≤ F) (hQ₁ : 0 ≤ Q₁) (hQ₂ : 0 ≤ Q₂) (hZ : 0 ≤ Z) (hE : 0 ≤ E)
    (h1 : Q₁ ≤ R*(x+N/d₁)) (h2 : Q₂ ≤ R*(x+N/d₂))
    (hscale : F ≤ κ*(M/N)*min 1 (N/(Real.sqrt (M*B)*(d₁*d₂)))) :
    F*Real.sqrt (Z*(d₁*d₂)*Q₁*Q₂*E*E) ≤
      κ*R*Real.sqrt (Z*E*E)*(M+Real.sqrt (M/B)*x) := by
  have hb := dual_range_bootstrap_scale hM hN hB hx hd₁ hd₂ hR hκ hF hQ₁ hQ₂ h1 h2 hscale
  rw [show Z*(d₁*d₂)*Q₁*Q₂*E*E = (Z*E*E)*((d₁*d₂)*Q₁*Q₂) by ring,
    Real.sqrt_mul (by positivity : 0 ≤ Z*E*E)]
  have hh := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg (Z*E*E))
  convert hh using 1 <;> ring

theorem dual_zero_active_range_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M H T x R A : ℝ) (K j e D N : ℕ)
      (S : Finset ℕ) (a : ℕ → ℂ) (c : ℤ) (g : ℕ → ℕ → ℂ),
      0 < M → 0 < H → 1 ≤ T → 0 ≤ x → 0 ≤ R → 0 ≤ A → 0 < e → 0 < D → 0 < N →
      (N : ℝ) ≤ 2*H → S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S, H ≤ (n : ℝ)) →
      (∀ q : ℕ, 0 < q → quadraticNorm (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/q)) ≤
        R*(x+(N : ℝ)/q)) →
      (∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ binarySquarefreeRows K j, ‖g d v‖ ≤ A) →
      (∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ binarySquarefreeRows K j, g d v ≠ 0 →
        (d : ℝ) ≤ dualWindowUpper M H T e v) →
      ‖∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ binarySquarefreeRows K j,
        ((M/e : ℝ) : ℂ)*g d v*gaussProductDivisorJacobiRow S S a (fun n => conj (a n)) c d (v : ℤ)‖ ≤
        (8*A*T*R)*Real.sqrt (C*(N : ℝ)^ε*coefficientEnergy S a*coefficientEnergy S a)*
          (M+Real.sqrt (M/(2^j : ℕ))*x) := by
  obtain ⟨C,hC,hbound⟩ := dual_gauss_weighted_range_bounds ε hε
  refine ⟨C,hC,?_⟩
  intro M H T x R A K j e D N S a c g hM hH hT hx hR hA he hD hN hNH hS hSH hnorm hg hsupp
  have hTp : 0 < T := by linarith
  have hep : (0 : ℝ) < e := by exact_mod_cast he
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  have hB : (0 : ℝ) < (2^j : ℕ) := by positivity
  have hrows : ∀ v ∈ binarySquarefreeRows K j, Odd v := fun v hv =>
    (mem_oddSquarefreeUpTo.mp (Finset.mem_filter.mp hv).1).2.2.1
  have hE := coefficientEnergy_nonneg S a
  by_cases hactive : ∃ d ∈ Finset.Ioc D (2*D), ∃ v ∈ binarySquarefreeRows K j, g d v ≠ 0
  · obtain ⟨d,hd,v,hv,hnz⟩ := hactive
    obtain ⟨p,hp,hrow⟩ := hbound D N (binarySquarefreeRows K j) S H hD hN hH hrows hS hSH
    obtain ⟨hp1,hp2,hplo,hphi,hpu1,hpu2⟩ := mem_divisorRangeScales.mp hp
    have hp1r : (1 : ℝ) ≤ p.1 := by exact_mod_cast hp1
    have hp2r : (1 : ℝ) ≤ p.2 := by exact_mod_cast hp2
    have hPr : (0 : ℝ) < (p.1 : ℝ)*p.2 := by positivity
    have hPD : (p.1 : ℝ)*p.2 ≤ 2*D := by exact_mod_cast hphi
    have hdcut := hsupp d hd v hv hnz
    rw [dualWindowUpper, squarefreeDyadicBase_eq_of_mem hv] at hdcut
    have hDd : (D : ℝ) ≤ d := by exact_mod_cast (Finset.mem_Ioc.mp hd).1.le
    have hcut : (p.1 : ℝ)*p.2 ≤ 4*T*Real.sqrt ((e : ℝ)*H^2/(M*(2^j : ℕ))) := by nlinarith
    have hscale := dual_zero_min_scale hM hNp hB hH he1 hT hPr hNH hcut
    have hQ1 := quadraticNorm_nonneg (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/p.1))
    have hQ2 := quadraticNorm_nonneg (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/p.2))
    have hboot := dual_range_energy_bootstrap hM hNp hB hx hp1r hp2r hR
      (show 0 ≤ 4*T by positivity) (show 0 ≤ M/((e : ℝ)*H) by positivity)
      hQ1 hQ2 (show 0 ≤ C*(N : ℝ)^ε by positivity) hE (hnorm p.1 hp1) (hnorm p.2 hp2) hscale
    have hw : ∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ binarySquarefreeRows K j,
        ‖((M/e : ℝ) : ℂ)*g d v‖ ≤ (M/e)*A := by
      intro d hd v hv
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (div_pos hM hep)]
      exact mul_le_mul_of_nonneg_left (hg d hd v hv) (by positivity)
    apply ((hrow a c (fun d v => ((M/e : ℝ) : ℂ)*g d v) ((M/e)*A) (by positivity) hw).1).trans
    have hh := mul_le_mul_of_nonneg_left hboot (show 0 ≤ 2*A by positivity)
    convert hh using 1 <;> push_cast <;> ring
  · have hz : ∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ binarySquarefreeRows K j, g d v = 0 := by
      intro d hd v hv
      by_contra hnz
      exact hactive ⟨d,hd,v,hv,hnz⟩
    have heq : (∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ binarySquarefreeRows K j,
        ((M/e : ℝ) : ℂ)*g d v*gaussProductDivisorJacobiRow S S a (fun n => conj (a n)) c d (v : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      apply Finset.sum_eq_zero
      intro v hv
      rw [hz d hd v hv]
      ring
    rw [heq,norm_zero]
    positivity

theorem dual_large_weight_le {M e B A : ℝ} {D d v : ℕ} (g : ℂ)
    (hM : 0 < M) (he : 0 < e) (hB : 0 < B) (_hA : 0 ≤ A) (hD : 0 < D)
    (hDd : D ≤ d) (hBv : B ≤ (v : ℝ)) (hg : ‖g‖ ≤ A) :
    ‖((Real.sqrt (M/(e*v))/d : ℝ) : ℂ)*g‖ ≤ (Real.sqrt (M/(e*B))/D)*A := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hD.trans_le hDd
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  have hvp : (0 : ℝ) < v := hB.trans_le hBv
  have hroot : Real.sqrt (M/(e*v)) ≤ Real.sqrt (M/(e*B)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hM.le (by positivity)
      (mul_le_mul_of_nonneg_left hBv he.le))
  have hquot := div_le_div₀ (Real.sqrt_nonneg _) hroot hDp (show (D : ℝ) ≤ d by exact_mod_cast hDd)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact mul_le_mul hquot hg (norm_nonneg _) (by positivity)

theorem dual_large_active_range_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M H T x R A : ℝ) (K j e D N : ℕ)
      (S : Finset ℕ) (a : ℕ → ℂ) (c : ℤ) (g : ℕ → ℕ → ℂ),
      0 < M → 0 < H → 1 ≤ T → 0 ≤ x → 0 ≤ R → 0 ≤ A → 0 < e → 0 < D → 0 < N →
      (N : ℝ) ≤ 2*H → S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S, H ≤ (n : ℝ)) →
      (∀ q : ℕ, 0 < q → quadraticNorm (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/q)) ≤
        R*(x+(N : ℝ)/q)) →
      (∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ binarySquarefreeRows K j, ‖g d v‖ ≤ A) →
      (∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ binarySquarefreeRows K j, g d v ≠ 0 →
        dualWindowLower M H T e v < (d : ℝ)) →
      ‖∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ binarySquarefreeRows K j,
        ((Real.sqrt (M/((e : ℝ)*v))/d : ℝ) : ℂ)*g d v*
          gaussProductDivisorJacobiRow S S (sqrtCoefficients a)
            (sqrtCoefficients (fun n => conj (a n))) c d (v : ℤ)‖ ≤
        (32*A*T*R)*Real.sqrt (C*(N : ℝ)^ε*coefficientEnergy S a*coefficientEnergy S a)*
          (M+Real.sqrt (M/(2^j : ℕ))*x) := by
  obtain ⟨C,hC,hbound⟩ := dual_gauss_weighted_range_bounds ε hε
  refine ⟨C,hC,?_⟩
  intro M H T x R A K j e D N S a c g hM hH hT hx hR hA he hD hN hNH hS hSH hnorm hg hsupp
  have hTp : 0 < T := by linarith
  have hep : (0 : ℝ) < e := by exact_mod_cast he
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  have hB : (0 : ℝ) < (2^j : ℕ) := by positivity
  have hrows : ∀ v ∈ binarySquarefreeRows K j, Odd v ∧ ((2^j : ℕ) : ℝ) ≤ v := by
    intro v hv
    obtain ⟨hv',hlo,hhi⟩ := Finset.mem_filter.mp hv
    exact ⟨(mem_oddSquarefreeUpTo.mp hv').2.2.1,by exact_mod_cast hlo⟩
  have hE := coefficientEnergy_nonneg S a
  by_cases hactive : ∃ d ∈ Finset.Ioc D (2*D), ∃ v ∈ binarySquarefreeRows K j, g d v ≠ 0
  · obtain ⟨d,hd,v,hv,hnz⟩ := hactive
    obtain ⟨p,hp,hrow⟩ := hbound D N (binarySquarefreeRows K j) S H hD hN hH
      (fun v hv => (hrows v hv).1) hS hSH
    obtain ⟨hp1,hp2,hplo,hphi,hpu1,hpu2⟩ := mem_divisorRangeScales.mp hp
    have hp1r : (1 : ℝ) ≤ p.1 := by exact_mod_cast hp1
    have hp2r : (1 : ℝ) ≤ p.2 := by exact_mod_cast hp2
    have hPr : (0 : ℝ) < (p.1 : ℝ)*p.2 := by positivity
    have hPD : (p.1 : ℝ)*p.2 ≤ 2*D := by exact_mod_cast hphi
    have hdcut := hsupp d hd v hv hnz
    rw [dualWindowLower, squarefreeDyadicBase_eq_of_mem hv] at hdcut
    have hdD : (d : ℝ) ≤ 2*D := by exact_mod_cast (Finset.mem_Ioc.mp hd).2
    have hcut : Real.sqrt ((e : ℝ)*H^2/(M*(2^j : ℕ))) ≤ 4*T*D := by
      have hh := (div_lt_iff₀ (show 0 < 2*T by positivity)).mp hdcut
      have hmul := mul_le_mul_of_nonneg_right hdD (show 0 ≤ 2*T by positivity)
      nlinarith
    have hscale := dual_reciprocal_min_scale hM hNp hB hH he1 hT hPr hDp hNH hPD hcut
    have hQ1 := quadraticNorm_nonneg (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/p.1))
    have hQ2 := quadraticNorm_nonneg (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/p.2))
    have hboot := dual_range_energy_bootstrap hM hNp hB hx hp1r hp2r hR
      (show 0 ≤ 16*T by positivity)
      (show 0 ≤ ((N : ℝ)/H)*(Real.sqrt (M/((e : ℝ)*(2^j : ℕ)))/D) by positivity)
      hQ1 hQ2 (show 0 ≤ C*(N : ℝ)^ε by positivity) hE (hnorm p.1 hp1) (hnorm p.2 hp2) hscale
    have hw : ∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ binarySquarefreeRows K j,
        ‖((Real.sqrt (M/((e : ℝ)*v))/d : ℝ) : ℂ)*g d v‖ ≤
          (Real.sqrt (M/((e : ℝ)*(2^j : ℕ)))/D)*A := by
      intro d hd v hv
      exact dual_large_weight_le (g d v) hM hep hB hA hD
        (Finset.mem_Ioc.mp hd).1.le (hrows v hv).2 (hg d hd v hv)
    apply ((hrow a c (fun d v => ((Real.sqrt (M/((e : ℝ)*v))/d : ℝ) : ℂ)*g d v)
      ((Real.sqrt (M/((e : ℝ)*(2^j : ℕ)))/D)*A) (by positivity) hw).2).trans
    have hh := mul_le_mul_of_nonneg_left hboot (show 0 ≤ 2*A by positivity)
    convert hh using 1 <;> push_cast <;> ring
  · have hz : ∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ binarySquarefreeRows K j, g d v = 0 := by
      intro d hd v hv
      by_contra hnz
      exact hactive ⟨d,hd,v,hv,hnz⟩
    have heq : (∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ binarySquarefreeRows K j,
        ((Real.sqrt (M/((e : ℝ)*v))/d : ℝ) : ℂ)*g d v*
          gaussProductDivisorJacobiRow S S (sqrtCoefficients a)
            (sqrtCoefficients (fun n => conj (a n))) c d (v : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      apply Finset.sum_eq_zero
      intro v hv
      rw [hz d hd v hv]
      ring
    rw [heq,norm_zero]
    positivity

end Ostmann.QuadraticSieve

end OAI
