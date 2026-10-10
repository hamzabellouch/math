import OAI.NumberTheory.Ostmann.Quadratic.QuadraticEulerCancellation

namespace OAI

/-! # The actual integer coefficients in the quadratic main-term comparison -/

namespace Ostmann

open scoped Classical BigOperators
open MonoidAlgebra

noncomputable def quadraticMainAlpha (D K w : ℕ) : ℤ :=
  ∑ e ∈ D.divisors, ∑ b ∈ oddSquarefreeRange K,
    if e * b = w then ArithmeticFunction.moebius e else 0

noncomputable def quadraticMainBeta (D K w : ℕ) : ℤ :=
  ∑ u ∈ D.divisors, ∑ v ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
    if u ^ 2 * v = w then ArithmeticFunction.moebius u else 0

noncomputable def quadraticMainGamma (D K w : ℕ) : ℤ :=
  quadraticMainAlpha D K w - quadraticMainBeta D K w

 theorem quadratic_euler_coefficient {D R : ℕ} (hD : Squarefree D)
    (hR : Squarefree R) (hDR : D.Coprime R) (w : ℕ) :
    (∑ e ∈ D.divisors, ∑ b ∈ (D * R).divisors,
      if e * b = w then ArithmeticFunction.moebius e else 0) =
    ∑ u ∈ D.divisors, ∑ v ∈ R.divisors,
      if u ^ 2 * v = w then ArithmeticFunction.moebius u else 0 := by
  have hh := congrArg (fun f : MonoidAlgebra ℤ ℕ => f.coeff w)
    (quadratic_euler_cancellation hD hR hDR)
  simp only [Finset.sum_mul, Finset.mul_sum, MonoidAlgebra.single_mul_single,
    mul_one, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply] at hh
  calc
    _ = ∑ b ∈ (D * R).divisors, ∑ e ∈ D.divisors,
        if e * b = w then ArithmeticFunction.moebius e else 0 := Finset.sum_comm
    _ = _ := hh
    _ = _ := Finset.sum_comm

/-- Once the finite Euler product contains the small squarefree integers, its
coefficient identity applies to the literal cutoffs used in the main terms. -/
theorem quadratic_main_coefficient_eq_of_cover {D R K w : ℕ}
    (hD : Squarefree D) (hR : Squarefree R) (hDR : D.Coprime R)
    (hDo : Odd D) (hRo : Odd R)
    (hcover : oddSquarefreeRange K ⊆ (D * R).divisors) (hw : w ≤ K) :
    quadraticMainAlpha D K w = quadraticMainBeta D K w := by
  have hproduct := (Nat.squarefree_mul hDR).mpr ⟨hD, hR⟩
  have hcoverR : (oddSquarefreeRange K).filter (D.Coprime ·) ⊆ R.divisors := by
    intro v hv
    obtain ⟨hv, hcop⟩ := Finset.mem_filter.mp hv
    have hd := Nat.dvd_of_mem_divisors (hcover hv)
    exact Nat.mem_divisors.mpr ⟨hcop.symm.dvd_of_dvd_mul_left hd, hR.ne_zero⟩
  have halpha : quadraticMainAlpha D K w =
      ∑ e ∈ D.divisors, ∑ b ∈ (D * R).divisors,
        if e * b = w then ArithmeticFunction.moebius e else 0 := by
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_subset hcover
    intro b hb hn
    have hbpos := Nat.pos_of_mem_divisors hb
    have hbs := hproduct.squarefree_of_dvd (Nat.dvd_of_mem_divisors hb)
    have hbo := (hDo.mul hRo).of_dvd_nat (Nat.dvd_of_mem_divisors hb)
    have hne : e * b ≠ w := by
      intro heq
      have hbK : b ≤ K := (Nat.le_mul_of_pos_left b (Nat.pos_of_mem_divisors he)).trans
        (heq ▸ hw)
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hbpos, hbK⟩, hbo, hbs⟩)
    exact ite_eq_right hne
  have hbeta : quadraticMainBeta D K w =
      ∑ u ∈ D.divisors, ∑ v ∈ R.divisors,
        if u ^ 2 * v = w then ArithmeticFunction.moebius u else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_subset hcoverR
    intro v hv hn
    have hvpos := Nat.pos_of_mem_divisors hv
    have hvs := hR.squarefree_of_dvd (Nat.dvd_of_mem_divisors hv)
    have hvo := hRo.of_dvd_nat (Nat.dvd_of_mem_divisors hv)
    have hcop : D.Coprime v := hDR.of_dvd_right (Nat.dvd_of_mem_divisors hv)
    have hne : u ^ 2 * v ≠ w := by
      intro heq
      have hvK : v ≤ K := (Nat.le_mul_of_pos_left v
        (pow_pos (Nat.pos_of_mem_divisors hu) 2)).trans (heq ▸ hw)
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hvpos, hvK⟩, hvo, hvs⟩, hcop⟩)
    exact ite_eq_right hne
  rw [halpha, hbeta]
  exact quadratic_euler_coefficient hD hR hDR w

end Ostmann

end OAI
