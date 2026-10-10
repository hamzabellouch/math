import OAI.Probability.InvariantIsing.Cavity.CavityResolventDerivative

namespace OAI

/-! The finite real-matrix Jacobi formula needed for the logarithmic
quadratic normalizer in the cavity calculation. -/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace InvariantIsing

private lemma cavity_determinant_derivative_identity {d : ℕ}
    (M : ℝ → Matrix (Fin d) (Fin d) ℝ) (M' : Matrix (Fin d) (Fin d) ℝ) (x : ℝ)
    (hx : M x = 1) (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) x) :
    HasDerivAt (fun t => (M t).det) (Matrix.trace M') x := by
  classical
  have hp (σ : Equiv.Perm (Fin d)) :
      HasDerivAt (fun t => ∏ i, M t (σ i) i)
        (if σ = 1 then Matrix.trace M' else 0) x := by
    have h := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hM (σ i) i)
    convert! h using 1
    by_cases hσ : σ = 1
    · subst σ
      simp only [ite_true, hx, Equiv.Perm.one_apply, Matrix.one_apply_eq,
        Finset.prod_const_one, one_smul, Matrix.trace, Matrix.diag_apply]
    · simp only [ite_eq_right hσ]
      symm
      apply Finset.sum_eq_zero
      intro i _
      obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne
        (Equiv.Perm.one_lt_card_support_of_ne_one hσ) i
      have hmove : σ j ≠ j := Equiv.Perm.mem_support.mp hj
      have hz : (∏ k ∈ Finset.univ.erase i, M x (σ k) k) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩)
        rw [hx, Matrix.one_apply_ne hmove]
      rw [hz, zero_smul]
  have hterm (σ : Equiv.Perm (Fin d)) := (hp σ).const_mul ((σ.sign : ℤ) : ℝ)
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ => hterm σ)
  have hfun : (fun t => (M t).det) =
      (fun t => ∑ σ : Equiv.Perm (Fin d), ((σ.sign : ℤ) : ℝ) * ∏ i, M t (σ i) i) := by
    funext t
    exact Matrix.det_apply' (M t)
  rw [hfun]
  convert! h using 1
  simp

theorem hasDerivAt_cavityDeterminant {d : ℕ}
    (M : ℝ → Matrix (Fin d) (Fin d) ℝ) (M' : Matrix (Fin d) (Fin d) ℝ) (x : ℝ)
    (hdet : IsUnit (M x).det) (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) x) :
    HasDerivAt (fun t => (M t).det) ((M x).det * Matrix.trace ((M x)⁻¹ * M')) x := by
  let Z : ℝ → Matrix (Fin d) (Fin d) ℝ := fun t => (M x)⁻¹ * M t
  have hZ : ∀ i j, HasDerivAt (fun t => Z t i j) (((M x)⁻¹ * M') i j) x := by
    intro i j
    have h := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (hM k j).const_mul ((M x)⁻¹ i k))
    exact h
  have hZx : Z x = 1 := Matrix.nonsing_inv_mul _ hdet
  have hz := cavity_determinant_derivative_identity Z ((M x)⁻¹ * M') x hZx hZ
  have h := hz.const_mul (M x).det
  have hfun : (fun t => (M t).det) = (fun t => (M x).det * (Z t).det) := by
    funext t
    dsimp only [Z]
    rw [Matrix.det_mul, ← mul_assoc, mul_comm (M x).det (M x)⁻¹.det, Matrix.det_nonsing_inv_mul_det _ hdet, one_mul]
  rw [hfun]
  exact h

theorem hasDerivAt_cavityLogDeterminant {d : ℕ}
    (M : ℝ → Matrix (Fin d) (Fin d) ℝ) (M' : Matrix (Fin d) (Fin d) ℝ) (x : ℝ)
    (hdet : IsUnit (M x).det) (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) x) :
    HasDerivAt (fun t => Real.log (M t).det) (Matrix.trace ((M x)⁻¹ * M')) x := by
  have hn : (M x).det ≠ 0 := isUnit_iff_ne_zero.mp hdet
  have h := (hasDerivAt_cavityDeterminant M M' x hdet hM).log hn
  convert! h using 1
  field_simp [hn]

lemma cavity_matrix_entry_derivative {d : ℕ}
    (M : ℝ → Matrix (Fin d) (Fin d) ℝ) (M' : Matrix (Fin d) (Fin d) ℝ) (x : ℝ)
    (hM : HasDerivAt M M' x) (i j : Fin d) :
    HasDerivAt (fun t => M t i j) (M' i j) x := by
  let P : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun A => A i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact (P.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt x hM

/-- The exact root-trace derivative for the normalizer, without a
commutation assumption on the covariance derivative and coefficient. -/
theorem hasDerivAt_cavityQuadraticLogDet {d : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (H' : Matrix (Fin d) (Fin d) ℝ) (x : ℝ)
    (hH : HasDerivAt H H' x) (hdet : IsUnit (1 - H x * K).det) :
    HasDerivAt (fun t => Real.log (1 - H t * K).det)
      (-Matrix.trace (H' * cavityBackwardQuadratic K (H x))) x := by
  have hD : HasDerivAt (fun t => 1 - H t * K) (-(H' * K)) x := by
    simpa only [zero_sub] using (hH.mul_const K).const_sub 1
  have h := hasDerivAt_cavityLogDeterminant _ _ x hdet
    (cavity_matrix_entry_derivative _ _ x hD)
  convert! h using 1
  change -Matrix.trace (H' * (K * (1 - H x * K)⁻¹)) = _
  rw [Matrix.mul_neg, Matrix.trace_neg, ← Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (H' * K) (1 - H x * K)⁻¹]

end InvariantIsing

end

end OAI
