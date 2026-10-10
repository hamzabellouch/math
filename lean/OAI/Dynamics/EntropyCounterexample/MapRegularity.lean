import OAI.Dynamics.EntropyCounterexample.Map
import OAI.Dynamics.EntropyCounterexample.PredictionInput
import OAI.Dynamics.EntropyCounterexample.LocalPredictionInput

namespace OAI

noncomputable section

namespace Problem340.Construction

def inputAngularFactor (D : SphereData) (n : ℕ) (z : Sphere) : ℂ :=
  (D.cutoff z : ℂ) * phase z ^ (2 ^ (n + 2))

theorem baseInput_eq_predictionSummand_tsum
    {E : Type*} (D : SphereData) (i : Fin 3) (t : E → ℝ) (z : E → Sphere) (x : E) :
    baseInput D i (t x) (z x) =
      ∑' n, predictionSummand (fun y => preparationCoeff (t y)) (readoutCoeff i)
        (fun n y => predictedClock D (n + 1) (t y) (z y))
        (fun n y => inputAngularFactor D n (z y)) D.L n x := by
  unfold baseInput
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [predictionSummand, inputTerm, inputAngularFactor, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

theorem exists_cutoff_fderiv_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ t, ‖fderiv ℝ preparationCoeff t‖ ≤ C) ∧
      ∀ i : Fin 3, ∀ t, ‖fderiv ℝ (readoutCoeff i) t‖ ≤ C := by
  have hp : HasCompactSupport preparationCoeff := preparationBump.hasCompactSupport
  have hr (i : Fin 3) : HasCompactSupport (readoutCoeff i) := (readoutBump i).hasCompactSupport
  obtain ⟨P, hP⟩ := (hp.fderiv ℝ).exists_bound_of_continuous
    ((preparationCoeff_contDiff (n := 1)).continuous_fderiv (by norm_num))
  choose R hR using fun i : Fin 3 => (hr i |>.fderiv ℝ).exists_bound_of_continuous
    ((readoutCoeff_contDiff i (n := 1)).continuous_fderiv (by norm_num))
  obtain ⟨M, hM⟩ := (Set.finite_range R).bddAbove
  refine ⟨max 0 (max P M), le_max_left _ _, ?_, ?_⟩
  · intro t
    exact (hP t).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro i t
    exact (hR i t).trans ((hM ⟨i, rfl⟩).trans
      ((le_max_right _ _).trans (le_max_right _ _)))

theorem norm_inputAngularFactor_le_one (D : SphereData) (n : ℕ) (z : Sphere)
    (hχ : ‖D.cutoff z‖ ≤ 1) : ‖inputAngularFactor D n z‖ ≤ 1 := by
  rw [inputAngularFactor, norm_mul, Complex.norm_real, norm_pow]
  exact (mul_le_of_le_one_left (by positivity) hχ).trans
    (pow_le_one₀ (norm_nonneg _) (norm_phase_le_one z))

theorem contDiffOn_baseInput_of_chart_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : SphereData) (i : Fin 3) {s : Set E} (hs : IsOpen s)
    (t : E → ℝ) (z : E → Sphere) {J B K : ℝ}
    (hJ : 0 ≤ J) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hBL : B < D.L) (hL : 2 < D.L)
    (ht : ContDiffOn ℝ 1 t s)
    (ht₁ : ∀ x ∈ s, ‖fderiv ℝ t x‖ ≤ J)
    (hχ : ∀ x ∈ s, ‖D.cutoff (z x)‖ ≤ 1)
    (hT : ∀ n, ContDiffOn ℝ 1
      (fun x => predictedClock D (n + 1) (t x) (z x)) s)
    (hT₁ : ∀ n x, x ∈ s →
      ‖fderiv ℝ (fun y => predictedClock D (n + 1) (t y) (z y)) x‖ ≤ B ^ (n + 1))
    (hΦ : ∀ n, ContDiffOn ℝ 1 (fun x => inputAngularFactor D n (z x)) s)
    (hΦ₁ : ∀ n x, x ∈ s →
      ‖fderiv ℝ (fun y => inputAngularFactor D n (z y)) x‖ ≤
        K * (1 + 2 ^ (n + 2))) :
    ContDiffOn ℝ 1 (fun x => baseInput D i (t x) (z x)) s := by
  obtain ⟨C, hC, hP, hR⟩ := exists_cutoff_fderiv_bound
  have heq : (fun x => baseInput D i (t x) (z x)) =
      (fun x => ∑' n, predictionSummand (fun y => preparationCoeff (t y)) (readoutCoeff i)
        (fun n y => predictedClock D (n + 1) (t y) (z y))
        (fun n y => inputAngularFactor D n (z y)) D.L n x) :=
    funext (baseInput_eq_predictionSummand_tsum D i t z)
  rw [heq]
  apply contDiffOn_one_predictionInput hs (A := C * J) (D := C) (K := K) (B := B)
    (mul_nonneg hC hJ) hC hK hB hBL hL
    (preparationCoeff_contDiff.comp_contDiffOn ht) (readoutCoeff_contDiff i) hT hΦ
  · intro x hx
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (preparationCoeff_nonneg _)] using
      preparationCoeff_le_one (t x)
  · intro u
    simpa only [Real.norm_eq_abs, abs_of_nonneg (readoutCoeff_nonneg i _)] using
      readoutCoeff_le_one i u
  · intro n x hx
    exact norm_inputAngularFactor_le_one D n (z x) (hχ x hx)
  · intro x hx
    have hdiff := (ht.differentiableOn_one x hx).differentiableAt (hs.mem_nhds hx)
    exact (norm_fderiv_comp_le
      ((preparationCoeff_contDiff (n := 1)).differentiable_one _) hdiff).trans
      (mul_le_mul (hP _) (ht₁ x hx) (norm_nonneg _) hC)
  · exact hR i
  · exact hT₁
  · exact hΦ₁

theorem contDiffOn_baseInput_of_scaled_chart_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : SphereData) (i : Fin 3) {s : Set E} (hs : IsOpen s)
    (t : E → ℝ) (z : E → Sphere) {J P B K : ℝ}
    (hJ : 0 ≤ J) (hP : 0 ≤ P) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hBL : B < D.L) (hL : 2 < D.L)
    (ht : ContDiffOn ℝ 1 t s)
    (ht₁ : ∀ x ∈ s, ‖fderiv ℝ t x‖ ≤ J)
    (hχ : ∀ x ∈ s, ‖D.cutoff (z x)‖ ≤ 1)
    (hT : ∀ n, ContDiffOn ℝ 1
      (fun x => predictedClock D (n + 1) (t x) (z x)) s)
    (hT₁ : ∀ n x, x ∈ s →
      ‖fderiv ℝ (fun y => predictedClock D (n + 1) (t y) (z y)) x‖ ≤ P * B ^ (n + 1))
    (hΦ : ∀ n, ContDiffOn ℝ 1 (fun x => inputAngularFactor D n (z x)) s)
    (hΦ₁ : ∀ n x, x ∈ s →
      ‖fderiv ℝ (fun y => inputAngularFactor D n (z y)) x‖ ≤
        K * (1 + 2 ^ (n + 2))) :
    ContDiffOn ℝ 1 (fun x => baseInput D i (t x) (z x)) s := by
  obtain ⟨C, hC, hPrep, hRead⟩ := exists_cutoff_fderiv_bound
  have heq : (fun x => baseInput D i (t x) (z x)) =
      (fun x => ∑' n, predictionSummand (fun y => preparationCoeff (t y)) (readoutCoeff i)
        (fun n y => predictedClock D (n + 1) (t y) (z y))
        (fun n y => inputAngularFactor D n (z y)) D.L n x) :=
    funext (baseInput_eq_predictionSummand_tsum D i t z)
  rw [heq]
  apply contDiffOn_predictionInput hs (A := C * J) (D := C) (J := P) (K := K) (B := B)
    (mul_nonneg hC hJ) hC hP hK hB hBL hL
    (preparationCoeff_contDiff.comp_contDiffOn ht) (readoutCoeff_contDiff i) hT hΦ
  · intro x hx
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (preparationCoeff_nonneg _)] using
      preparationCoeff_le_one (t x)
  · intro n x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (readoutCoeff_nonneg i _)] using
      readoutCoeff_le_one i _
  · intro n x hx
    exact norm_inputAngularFactor_le_one D n (z x) (hχ x hx)
  · intro x hx
    have hdiff := (ht.differentiableOn_one x hx).differentiableAt (hs.mem_nhds hx)
    exact (norm_fderiv_comp_le
      ((preparationCoeff_contDiff (n := 1)).differentiable_one _) hdiff).trans
      (mul_le_mul (hPrep _) (ht₁ x hx) (norm_nonneg _) hC)
  · intro n x hx
    exact hRead i _
  · exact hT₁
  · exact hΦ₁

end Problem340.Construction

end

end OAI
