import OAI.NumberTheory.DirichletL.RayQuotient
import OAI.NumberTheory.DirichletL.IdealLogDerivative

namespace OAI

namespace SevenEighths.PNT.RayAsymptotic

open ActualEisensteinCubic RayOrthogonality Filter
open scoped BigOperators Classical Topology

noncomputable section

variable (M : Ideal O) [Finite (O ⧸ M)]

def classCoeff (n : ℕ) : ℝ := IdealMangoldt.classCoeff (principalIdeals M) n

theorem sum_coeff (n : ℕ) :
    (∑ χ : rayCharacters M, IdealLogDerivative.coeff (idealCharacter M χ) n) =
      (rayCard M : ℂ) * (classCoeff M n : ℂ) := by
  unfold IdealLogDerivative.coeff ShortDraftHeckeBridge.normFiberCoeff
  rw [Finset.sum_comm]
  unfold classCoeff IdealMangoldt.classCoeff IdealMangoldt.coeff IdealMangoldt.normFiber
  rw [Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [← Finset.mul_sum, sum_idealCharacters]
  by_cases hI : I ∈ principalIdeals M
  · simp only [hI, ite_true, one_mul, mul_comm]
  · simp only [hI, ite_false, zero_mul, Complex.ofReal_zero, mul_zero]

theorem average_coeff (n : ℕ) :
    (classCoeff M n : ℂ) =
      (∑ χ : rayCharacters M, IdealLogDerivative.coeff (idealCharacter M χ) n) /
        (rayCard M : ℂ) := by
  rw [sum_coeff]
  have hc : (rayCard M : ℂ) ≠ 0 := by exact_mod_cast (rayCard_pos M).ne'
  exact (mul_div_cancel_left₀ _ hc).symm

theorem classCoeff_LSeries (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (classCoeff M n : ℂ)) s =
      (∑ χ : rayCharacters M, LSeries (IdealLogDerivative.coeff (idealCharacter M χ)) s) /
        (rayCard M : ℂ) := by
  have heq : (fun n => (classCoeff M n : ℂ)) =
      (rayCard M : ℂ)⁻¹ • ∑ χ : rayCharacters M, IdealLogDerivative.coeff (idealCharacter M χ) := by
    funext n
    rw [average_coeff]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq, LSeries_smul, LSeries_sum]
  · rw [div_eq_mul_inv, mul_comm]
  · intro χ _
    exact IdealLogDerivative.coeff_summable _ (norm_idealCharacter_le_one M χ) s hs

def principalRegularization (F : ℂ → ℂ) (residue : ℂ) : ℂ → ℂ :=
  Function.update (fun s => (s - 1) * F s) 1 residue

omit [Finite (O ⧸ M)] in
theorem principalRegularization_eventuallyEq (F : ℂ → ℂ) (residue : ℂ)
    {s : ℂ} (hs : s ≠ 1) :
    principalRegularization F residue =ᶠ[𝓝 s] (fun z => (z - 1) * F z) := by
  refine eventuallyEq_iff_exists_mem.mpr ?_
  exact ⟨_, isOpen_ne.mem_nhds hs, fun z hz => Function.update_of_ne (Set.mem_ofPred.mp hz) ..⟩

omit [Finite (O ⧸ M)] in
theorem principalRegularization_analyticAt (F : ℂ → ℂ) (residue : ℂ)
    {s : ℂ} (hs : s ≠ 1) (hF : AnalyticAt ℂ F s) :
    AnalyticAt ℂ (principalRegularization F residue) s :=
  ((analyticAt_id.sub analyticAt_const).mul hF).congr
    (principalRegularization_eventuallyEq F residue hs).symm

omit [Finite (O ⧸ M)] in

theorem principalRegularization_analyticAt_of_local (F R : ℂ → ℂ)
    (hR : AnalyticAt ℂ R 1)
    (hFR : ∀ᶠ s in 𝓝 (1 : ℂ), s ≠ 1 → (s - 1) * F s = R s) :
    AnalyticAt ℂ (principalRegularization F (R 1)) 1 := by
  apply hR.congr
  filter_upwards [hFR] with s hs
  by_cases hs1 : s = 1
  · subst s
    simp only [principalRegularization, Function.update_self]
  · rw [principalRegularization, Function.update_of_ne hs1]
    exact (hs hs1).symm

omit [Finite (O ⧸ M)] in
theorem principalRegularization_logDeriv (F : ℂ → ℂ) (residue : ℂ)
    {s : ℂ} (hs : s ≠ 1) (hF : AnalyticAt ℂ F s) (hF0 : F s ≠ 0) :
    -deriv (principalRegularization F residue) s / principalRegularization F residue s =
      -deriv F s / F s - 1 / (s - 1) := by
  have hd := (principalRegularization_eventuallyEq F residue hs).deriv_eq
  rw [hd, principalRegularization, Function.update_of_ne hs,
    deriv_fun_mul (by fun_prop) hF.differentiableAt, deriv_sub_const, deriv_id'', one_mul]
  field_simp
  ring

def regularizedFamily (F : rayCharacters M → ℂ → ℂ) (residue : ℂ)
    (χ : rayCharacters M) : ℂ → ℂ :=
  if χ = 1 then principalRegularization (F χ) residue else F χ

def remainder (F : rayCharacters M → ℂ → ℂ) (residue : ℂ) (s : ℂ) : ℂ :=
  (∑ χ : rayCharacters M,
    -deriv (regularizedFamily M F residue χ) s / regularizedFamily M F residue χ s) /
      (rayCard M : ℂ)

structure AnalyticFamily (F : rayCharacters M → ℂ → ℂ) (residue : ℂ) : Prop where
  eq_series : ∀ (χ : rayCharacters M) (s : ℂ), 1 < s.re →
    F χ s = IdealEuler.series (idealCharacter M χ) s
  analytic : ∀ (χ : rayCharacters M) (s : ℂ), 1 ≤ s.re →
    χ ≠ 1 ∨ s ≠ 1 → AnalyticAt ℂ (F χ) s
  nonzero : ∀ (χ : rayCharacters M) (s : ℂ), 1 ≤ s.re →
    χ ≠ 1 ∨ s ≠ 1 → F χ s ≠ 0
  pole_analytic : AnalyticAt ℂ (principalRegularization (F 1) residue) 1
  residue_ne_zero : residue ≠ 0

theorem regularizedFamily_analyticAt {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) (χ : rayCharacters M) (s : ℂ) (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (regularizedFamily M F residue χ) s := by
  by_cases hχ : χ = 1
  · subst χ
    rw [regularizedFamily, ite_eq_left rfl]
    by_cases hs1 : s = 1
    · subst s
      exact hF.pole_analytic
    · exact principalRegularization_analyticAt _ _ hs1 (hF.analytic 1 s hs (Or.inr hs1))
  · rw [regularizedFamily, ite_eq_right hχ]
    exact hF.analytic χ s hs (Or.inl hχ)

theorem regularizedFamily_ne_zero {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) (χ : rayCharacters M) (s : ℂ) (hs : 1 ≤ s.re) :
    regularizedFamily M F residue χ s ≠ 0 := by
  by_cases hχ : χ = 1
  · subst χ
    rw [regularizedFamily, ite_eq_left rfl]
    by_cases hs1 : s = 1
    · subst s
      simpa only [principalRegularization, Function.update_self] using hF.residue_ne_zero
    · rw [principalRegularization, Function.update_of_ne hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1) (hF.nonzero 1 s hs (Or.inr hs1))
  · rw [regularizedFamily, ite_eq_right hχ]
    exact hF.nonzero χ s hs (Or.inl hχ)

theorem remainder_continuousOn {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    ContinuousOn (remainder M F residue) {s : ℂ | 1 ≤ s.re} := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div_const
  apply tendsto_finsetSum
  intro χ _
  have h := regularizedFamily_analyticAt M hF χ s hs
  exact h.deriv.continuousAt.neg.div h.continuousAt (regularizedFamily_ne_zero M hF χ s hs)

theorem regularizedFamily_logDeriv {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) (χ : rayCharacters M) (s : ℂ) (hs : 1 < s.re) :
    -deriv (regularizedFamily M F residue χ) s / regularizedFamily M F residue χ s =
      -deriv (F χ) s / F χ s - (if χ = 1 then 1 / (s - 1) else 0) := by
  by_cases hχ : χ = 1
  · rw [regularizedFamily, ite_eq_left hχ, ite_eq_left hχ]
    have hs1 : s ≠ 1 := by intro heq; simp only [heq, Complex.one_re] at hs; linarith
    exact principalRegularization_logDeriv _ _ hs1
      (hF.analytic χ s hs.le (Or.inr hs1)) (hF.nonzero χ s hs.le (Or.inr hs1))
  · simp only [regularizedFamily, hχ, ite_false, sub_zero]

theorem remainder_eqOn {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    Set.EqOn (remainder M F residue)
      (fun s => LSeries (fun n => (classCoeff M n : ℂ)) s -
        (rayCard M : ℂ)⁻¹ / (s - 1)) {s : ℂ | 1 < s.re} := by
  intro s hs
  change remainder M F residue s = LSeries (fun n => (classCoeff M n : ℂ)) s -
    (rayCard M : ℂ)⁻¹ / (s - 1)
  rw [remainder, classCoeff_LSeries M s hs]
  simp_rw [regularizedFamily_logDeriv M hF _ s hs]
  rw [Finset.sum_sub_distrib]
  have hsum : (∑ χ : rayCharacters M, if χ = 1 then 1 / (s - 1) else (0 : ℂ)) =
      1 / (s - 1) := by simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hsum]
  have hlog (χ : rayCharacters M) : -deriv (F χ) s / F χ s =
      LSeries (IdealLogDerivative.coeff (idealCharacter M χ)) s :=
    (IdealLogDerivative.coeff_LSeries_eq_neg_logDeriv_of_eq _
      (norm_idealCharacter_le_one M χ) (F χ) (hF.eq_series χ) s hs).symm
  simp_rw [hlog]
  ring

theorem classCoeff_ratio_tendsto {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    Tendsto (fun N : ℕ => cumsum (classCoeff M) N / N)
      atTop (𝓝 ((rayCard M : ℝ)⁻¹)) := by
  apply WienerIkeharaTheorem'
    (IdealMangoldt.classCoeff_nonneg (principalIdeals M))
    (fun σ hσ => IdealMangoldt.classCoeff_summable_nterm (principalIdeals M) hσ)
    (IdealMangoldt.classCoeff_chebyshev (principalIdeals M))
    (remainder_continuousOn M hF)
  simpa only [classCoeff, Complex.ofReal_inv, Complex.ofReal_natCast] using remainder_eqOn M hF

section Quotient

variable (H : Subgroup (O ⧸ M)ˣ) (hH : globalUnits M ≤ H)

def quotientClassCoeff (n : ℕ) : ℝ := IdealMangoldt.classCoeff (RayQuotient.identityClass M H) n

theorem quotient_sum_coeff (n : ℕ) :
    (∑ χ : RayQuotient.Characters M H,
      IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ) n) =
      (RayQuotient.classNumber M H : ℂ) * (quotientClassCoeff M H n : ℂ) := by
  unfold IdealLogDerivative.coeff ShortDraftHeckeBridge.normFiberCoeff
  rw [Finset.sum_comm]
  unfold quotientClassCoeff IdealMangoldt.classCoeff IdealMangoldt.coeff IdealMangoldt.normFiber
  rw [Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [← Finset.mul_sum, RayQuotient.sum_idealCharacters]
  by_cases hI : I ∈ RayQuotient.identityClass M H
  · simp only [hI, ite_true, one_mul, mul_comm]
  · simp only [hI, ite_false, zero_mul, Complex.ofReal_zero, mul_zero]

theorem quotient_average_coeff (n : ℕ) :
    (quotientClassCoeff M H n : ℂ) =
      (∑ χ : RayQuotient.Characters M H,
        IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ) n) /
          (RayQuotient.classNumber M H : ℂ) := by
  rw [quotient_sum_coeff]
  have hc : (RayQuotient.classNumber M H : ℂ) ≠ 0 := by
    exact_mod_cast (RayQuotient.classNumber_pos M H).ne'
  exact (mul_div_cancel_left₀ _ hc).symm

theorem quotientClassCoeff_LSeries (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (quotientClassCoeff M H n : ℂ)) s =
      (∑ χ : RayQuotient.Characters M H,
        LSeries (IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ)) s) /
          (RayQuotient.classNumber M H : ℂ) := by
  have heq : (fun n => (quotientClassCoeff M H n : ℂ)) =
      (RayQuotient.classNumber M H : ℂ)⁻¹ • ∑ χ : RayQuotient.Characters M H,
        IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ) := by
    funext n
    rw [quotient_average_coeff M H hH]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq, LSeries_smul, LSeries_sum]
  · rw [div_eq_mul_inv, mul_comm]
  · intro χ _
    exact IdealLogDerivative.coeff_summable _ (RayQuotient.norm_idealCharacter_le_one M H hH χ) s hs

def quotientRemainder (F : rayCharacters M → ℂ → ℂ) (residue : ℂ) (s : ℂ) : ℂ :=
  (∑ χ : RayQuotient.Characters M H,
    -deriv (regularizedFamily M F residue (RayQuotient.toFullRay M H hH χ)) s /
      regularizedFamily M F residue (RayQuotient.toFullRay M H hH χ) s) /
        (RayQuotient.classNumber M H : ℂ)

theorem quotientRemainder_continuousOn {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    ContinuousOn (quotientRemainder M H hH F residue) {s : ℂ | 1 ≤ s.re} := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div_const
  apply tendsto_finsetSum
  intro χ _
  have h := regularizedFamily_analyticAt M hF (RayQuotient.toFullRay M H hH χ) s hs
  exact h.deriv.continuousAt.neg.div h.continuousAt
    (regularizedFamily_ne_zero M hF (RayQuotient.toFullRay M H hH χ) s hs)

theorem quotientRemainder_eqOn {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    Set.EqOn (quotientRemainder M H hH F residue)
      (fun s => LSeries (fun n => (quotientClassCoeff M H n : ℂ)) s -
        (RayQuotient.classNumber M H : ℂ)⁻¹ / (s - 1)) {s : ℂ | 1 < s.re} := by
  intro s hs
  change quotientRemainder M H hH F residue s =
    LSeries (fun n => (quotientClassCoeff M H n : ℂ)) s -
      (RayQuotient.classNumber M H : ℂ)⁻¹ / (s - 1)
  rw [quotientRemainder, quotientClassCoeff_LSeries M H hH s hs]
  simp_rw [regularizedFamily_logDeriv M hF _ s hs, RayQuotient.toFullRay_eq_one]
  rw [Finset.sum_sub_distrib]
  have hsum : (∑ χ : RayQuotient.Characters M H, if χ = 1 then 1 / (s - 1) else (0 : ℂ)) =
      1 / (s - 1) := by simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hsum]
  have hlog (χ : RayQuotient.Characters M H) :
      -deriv (F (RayQuotient.toFullRay M H hH χ)) s / F (RayQuotient.toFullRay M H hH χ) s =
        LSeries (IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ)) s := by
    rw [RayQuotient.idealCharacter_eq_fullRay]
    exact (IdealLogDerivative.coeff_LSeries_eq_neg_logDeriv_of_eq _
      (norm_idealCharacter_le_one M _) (F _) (hF.eq_series _) s hs).symm
  simp_rw [hlog]
  ring

include hH in

theorem quotientClassCoeff_ratio_tendsto {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    Tendsto (fun N : ℕ => cumsum (quotientClassCoeff M H) N / N)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹)) := by
  apply WienerIkeharaTheorem'
    (IdealMangoldt.classCoeff_nonneg (RayQuotient.identityClass M H))
    (fun σ hσ => IdealMangoldt.classCoeff_summable_nterm (RayQuotient.identityClass M H) hσ)
    (IdealMangoldt.classCoeff_chebyshev (RayQuotient.identityClass M H))
    (quotientRemainder_continuousOn M H hH hF)
  simpa only [quotientClassCoeff, Complex.ofReal_inv, Complex.ofReal_natCast]
    using quotientRemainder_eqOn M H hH hF

end Quotient

end
end SevenEighths.PNT.RayAsymptotic

end OAI
