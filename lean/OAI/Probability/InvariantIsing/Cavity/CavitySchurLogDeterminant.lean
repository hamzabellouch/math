import OAI.Probability.InvariantIsing.Cavity.CavitySchurMultiplicity

namespace OAI

/-! Finite spectral multiplicity bookkeeping for `cav:determinant`.
The diagonal comparison block has `n-s_a` copies of eigenvalue `a`. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_labeledSpectrum_determinant {d m : ℕ}
    (g : Fin d → Fin m) (lam : Fin m → ℝ) (b : ℝ) :
    (b • (1 : Matrix (Fin d) (Fin d) ℝ) - Matrix.diagonal (fun i => lam (g i))).det =
      ∏ a, (b - lam a) ^ ((Finset.univ.filter (fun i => g i = a)).card) := by
  have hshift : b • (1 : Matrix (Fin d) (Fin d) ℝ) - Matrix.diagonal (fun i => lam (g i)) =
      Matrix.diagonal (fun i => b - lam (g i)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hshift, Matrix.det_diagonal]
  rw [← Finset.prod_fiberwise' Finset.univ g (fun a => b - lam a)]
  simp only [Finset.prod_const]

private lemma cavity_missing_multiplicity_product {m : ℕ}
    (t : Fin m → ℝ) (ht : ∀ a, t a ≠ 0) (n : ℕ) (s : Fin m → ℕ)
    (hs : ∀ a, s a ≤ n) :
    (∏ a, t a ^ n) / (∏ a, t a ^ (n - s a)) = ∏ a, t a ^ s a := by
  have hden : (∏ a, t a ^ (n - s a)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun a _ => pow_ne_zero _ (ht a))
  apply (div_eq_iff hden).2
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  rw [← pow_add, Nat.add_sub_of_le (hs a)]

/-- The full finite multiplicity cancellation: the determinant ratio is
`x^n ∏_a (b-λ_a)^s_a`, before taking its logarithm. -/
theorem cavity_schur_tilt_det_multiplicity {d n m : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (g : Fin d → Fin m)
    (lam : Fin m → ℝ) (s : Fin m → ℕ) (hs : ∀ a, s a ≤ n)
    (hcounts : ∀ a, (Finset.univ.filter (fun i => g i = a)).card = n - s a)
    (b x : ℝ) (hx : x ≠ 0) (hb : ∀ a, lam a < b)
    (hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det)
    (hM : IsUnit (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C).det)
    (hcompression : ((b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C)⁻¹).toBlocks₂₂ = x • 1)
    (hfull : (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C).det = ∏ a, (b - lam a) ^ n) :
    (1 - (b • (1 : Matrix (Fin d) (Fin d) ℝ) - Matrix.diagonal (fun i => lam (g i)))⁻¹ *
      (A - Matrix.diagonal (fun i => lam (g i)))).det =
        x ^ n * ∏ a, (b - lam a) ^ s a := by
  have hdiag : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal (fun i => lam (g i))).det := by
    rw [cavity_labeledSpectrum_determinant]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
      (fun a _ => pow_ne_zero _ (ne_of_gt (sub_pos.mpr (hb a)))))
  rw [cavity_tilt_determinant_ratio A _ b hdiag,
    cavity_schur_det_of_scalar_compression A L C b x hx hA hM hcompression,
    hfull, cavity_labeledSpectrum_determinant]
  simp_rw [hcounts]
  rw [mul_div_assoc, cavity_missing_multiplicity_product _
    (fun a => ne_of_gt (sub_pos.mpr (hb a))) n s hs]

/-- Logarithmic multiplicity form used in the final cavity evaluation. -/
theorem cavity_log_multiplicity_product {m : ℕ}
    (lam rho : Fin m → ℝ) (s : Fin m → ℕ) (n : ℕ)
    (hrho : ∀ a, (s a : ℝ) = (n : ℝ) * rho a)
    (b x : ℝ) (hx : 0 < x) (hb : ∀ a, lam a < b) :
    Real.log (x ^ n * ∏ a, (b - lam a) ^ s a) =
      (n : ℝ) * (Real.log x + ∑ a, rho a * Real.log (b - lam a)) := by
  have hp : (∏ a, (b - lam a) ^ s a) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun a _ => pow_ne_zero _ (ne_of_gt (sub_pos.mpr (hb a))))
  rw [Real.log_mul (pow_ne_zero _ hx.ne') hp, Real.log_pow,
    Real.log_prod (fun a _ => pow_ne_zero _ (ne_of_gt (sub_pos.mpr (hb a))))]
  simp_rw [Real.log_pow, hrho]
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ring

end InvariantIsing

end

end OAI
