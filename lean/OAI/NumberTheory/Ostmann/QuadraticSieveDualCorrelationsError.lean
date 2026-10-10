import OAI.NumberTheory.Ostmann.QuadraticSieveDualCorrelationsLeading

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap

theorem dualSecondSquareMain_error (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ signedSquarefreeMultipliers,
      ∀ (M : ℝ) (e b q : ℕ), 0 < M → 0 < e → 0 < b → 2 ≤ q →
      ∀ (X₁ X₂ J L : ℕ → ℕ → ℝ),
        0 < X₁ e b → X₁ e b ≤ Real.sqrt ((e : ℝ)*q/(M*b)) →
        Real.sqrt ((e : ℝ)*q/(M*b)) ≤ X₂ e b → 0 < J e b →
        J e b ≤ min (Real.sqrt ((e : ℝ)*q/(M*b))/X₁ e b)
          (X₂ e b/Real.sqrt ((e : ℝ)*q/(M*b))) →
        (X₂ e b/Real.sqrt ((e : ℝ)*q/(M*b)))^2 ≤ L e b →
        ‖dualSquareSum W (s : ℝ) e M b q - dualSecondSquareMain W M e s b q X₁ X₂ L‖ ≤
          C * Real.sqrt ((e : ℝ)*q/(M*b)) / J e b^A := by
  classical
  have hex : ∀ s : ℤ, ∃ C : ℝ, 0 < C ∧ ∀ hs : s ∈ signedSquarefreeMultipliers,
      ∀ (M : ℝ) (e b q : ℕ), 0 < M → 0 < e → 0 < b → 2 ≤ q →
      ∀ (X₁ X₂ J L : ℕ → ℕ → ℝ),
        0 < X₁ e b → X₁ e b ≤ Real.sqrt ((e : ℝ)*q/(M*b)) →
        Real.sqrt ((e : ℝ)*q/(M*b)) ≤ X₂ e b → 0 < J e b →
        J e b ≤ min (Real.sqrt ((e : ℝ)*q/(M*b))/X₁ e b)
          (X₂ e b/Real.sqrt ((e : ℝ)*q/(M*b))) →
        (X₂ e b/Real.sqrt ((e : ℝ)*q/(M*b)))^2 ≤ L e b →
        ‖dualSquareSum W (s : ℝ) e M b q - dualSecondSquareMain W M e s b q X₁ X₂ L‖ ≤
          C * Real.sqrt ((e : ℝ)*q/(M*b)) / J e b^A := by
    intro s
    by_cases hs : s ∈ signedSquarefreeMultipliers
    · have hs0 := signedSquarefreeMultiplier_ne_zero hs
      have hsr : (s : ℝ) ≠ 0 := by exact_mod_cast hs0
      obtain ⟨C,hC,hbound⟩ := dualSquareSum_poisson_error W (s : ℝ) hsr A
      refine ⟨C,hC,?_⟩
      intro hsm M e b q hM he hb hq X₁ X₂ J L h1 h2 h3 hJ hmin hL
      rw [dualSecondSquareMain, dualSignedSquareWeight_eq W s hs0]
      exact hbound e M b q (by exact_mod_cast he) hM (by exact_mod_cast hb) hq
        (X₁ e b) (X₂ e b) (J e b) (L e b) h1 h2 h3 hJ hmin hL
    · exact ⟨1, by norm_num, fun hsm => (hs hsm).elim⟩
  choose C hC hbound using hex
  let D : ℝ := 1 + ∑ s ∈ signedSquarefreeMultipliers, C s
  have hD : 0 < D := by
    dsimp [D]
    have hsum : 0 ≤ ∑ s ∈ signedSquarefreeMultipliers, C s :=
      Finset.sum_nonneg (fun s hs => (hC s).le)
    linarith
  refine ⟨D,hD,?_⟩
  intro s hs M e b q hM he hb hq X₁ X₂ J L h1 h2 h3 hJ hmin hL
  have hCD : C s ≤ D := by
    have hh := Finset.single_le_sum (fun t ht => (hC t).le) hs
    dsimp [D]
    linarith
  exact (hbound s hs M e b q hM he hb hq X₁ X₂ J L h1 h2 h3 hJ hmin hL).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCD (Real.sqrt_nonneg _))
      (pow_nonneg hJ.le _))

theorem norm_dualCorrelationGaussFactor_le (M : ℝ) (hM : 0 < M) (e q : ℕ) [NeZero q]
    (he : 0 < e) (hq : Odd q) (hsq : Squarefree q) :
    ‖dualCorrelationGaussFactor M e q‖ ≤ (M/(e*q))*Real.sqrt (q : ℝ) := by
  have hep : (0 : ℝ) < e := by exact_mod_cast he
  have hqp : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_neZero q
  have hnorm : ‖gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar‖ = Real.sqrt (q : ℝ) := by
    rw [← quadratic_gauss_norm_sq hq hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [dualCorrelationGaussFactor_eq, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity), hnorm]
  calc
    _ ≤ 1 * (M/(e*q)) * Real.sqrt (q : ℝ) := by
      gcongr
      exact norm_moebius_complex_le_one e
    _ = _ := by ring

noncomputable def dualSecondErrorScale (M : ℝ) (Δ K q A : ℕ) (J : ℕ → ℕ → ℝ) : ℝ :=
  ∑ e ∈ (2*Δ).divisors, ∑ b ∈ oddSquarefreeUpTo K,
    (M/(e*q))*Real.sqrt (q : ℝ)*Real.sqrt ((e : ℝ)*q/(M*b))/J e b^A

theorem dualCorrelationRemainderTerm_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ) (Δ K q : ℕ) [NeZero q],
      0 < M → Odd q → Squarefree q → 2 ≤ q → ∀ (X₁ X₂ J L : ℕ → ℕ → ℝ),
      (∀ e ∈ (2*Δ).divisors, ∀ b ∈ oddSquarefreeUpTo K,
        0 < X₁ e b ∧ X₁ e b ≤ Real.sqrt ((e : ℝ)*q/(M*b)) ∧
        Real.sqrt ((e : ℝ)*q/(M*b)) ≤ X₂ e b ∧ 0 < J e b ∧
        J e b ≤ min (Real.sqrt ((e : ℝ)*q/(M*b))/X₁ e b)
          (X₂ e b/Real.sqrt ((e : ℝ)*q/(M*b))) ∧
        (X₂ e b/Real.sqrt ((e : ℝ)*q/(M*b)))^2 ≤ L e b) →
      ‖dualCorrelationRemainderTerm W M Δ K q X₁ X₂ L‖ ≤ C * dualSecondErrorScale M Δ K q A J := by
  obtain ⟨C,hC,hbound⟩ := dualSecondSquareMain_error W A
  refine ⟨4*C,by positivity,?_⟩
  intro M Δ K q _ hM hq hsq hq2 X₁ X₂ J L hp
  unfold dualCorrelationRemainderTerm
  calc
    _ ≤ ∑ e ∈ (2*Δ).divisors, ∑ s ∈ signedSquarefreeMultipliers, ∑ b ∈ oddSquarefreeUpTo K,
        ‖dualCorrelationGaussFactor M e q * (jacobiSym ((e : ℤ)*s*(b : ℤ)) q : ℂ) *
          (dualSquareSum W (s : ℝ) e M b q - dualSecondSquareMain W M e s b q X₁ X₂ L)‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e he
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun s hs => norm_sum_le _ _))
    _ ≤ ∑ e ∈ (2*Δ).divisors, ∑ s ∈ signedSquarefreeMultipliers, ∑ b ∈ oddSquarefreeUpTo K,
        C * ((M/(e*q))*Real.sqrt (q : ℝ)*Real.sqrt ((e : ℝ)*q/(M*b))/J e b^A) := by
      apply Finset.sum_le_sum
      intro e he
      have hep := Nat.pos_of_mem_divisors he
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨h1,h2,h3,hJ,hmin,hL⟩ := hp e he b hb
      have hbp := (mem_oddSquarefreeUpTo.mp hb).1
      have hfactor := norm_dualCorrelationGaussFactor_le M hM e q hep hq hsq
      have herror := hbound s hs M e b q hM hep hbp hq2 X₁ X₂ J L h1 h2 h3 hJ hmin hL
      have hj : ‖(jacobiSym ((e : ℤ)*s*(b : ℤ)) q : ℂ)‖ ≤ 1 := by
        rcases jacobiSym.trichotomy ((e : ℤ)*s*(b : ℤ)) q with h | h | h <;> simp [h]
      rw [norm_mul, norm_mul]
      calc
        _ ≤ ((M/(e*q))*Real.sqrt (q : ℝ)) * 1 *
            (C * Real.sqrt ((e : ℝ)*q/(M*b))/J e b^A) := by gcongr
        _ = _ := by ring
    _ = _ := by
      simp only [Finset.sum_const, card_signedSquarefreeMultipliers, nsmul_eq_mul,
        dualSecondErrorScale, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro b hb
      ring

end Ostmann.QuadraticSieve

end OAI
