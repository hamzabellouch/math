import Mathlib

namespace OAI

noncomputable section

namespace Problem340

section Estimates

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma norm_fderiv_real_smul_le {a : E → ℝ} {v : E → F} {x : E}
    (ha : DifferentiableAt ℝ a x) (hv : DifferentiableAt ℝ v x) :
    ‖fderiv ℝ (fun y => a y • v y) x‖ ≤
      ‖a x‖ * ‖fderiv ℝ v x‖ + ‖fderiv ℝ a x‖ * ‖v x‖ := by
  rw [fderiv_fun_smul ha hv]
  exact (norm_add_le _ _).trans_eq (by
    rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply])

lemma norm_fderiv_real_comp_le {a : ℝ → ℝ} {t : E → ℝ} {x : E}
    (ha : DifferentiableAt ℝ a (t x)) (ht : DifferentiableAt ℝ t x) :
    ‖fderiv ℝ (fun y => a (t y)) x‖ ≤
      ‖fderiv ℝ a (t x)‖ * ‖fderiv ℝ t x‖ := by
  rw [fderiv_fun_comp x ha ht]
  exact ContinuousLinearMap.opNorm_comp_le _ _

def predictionTerm (c : ℝ) (α β : ℝ → ℝ) (t T : E → ℝ) (Φ : E → F) (x : E) : F :=
  c • (α (t x) • (β (T x) • Φ x))

theorem norm_fderiv_prediction_product_le
    {a : E → ℝ} {β : ℝ → ℝ} {T : E → ℝ} {Φ : E → F} {x : E}
    {A D P Q : ℝ} (c : ℝ)
    (ha : DifferentiableAt ℝ a x) (hβ : DifferentiableAt ℝ β (T x))
    (hT : DifferentiableAt ℝ T x) (hΦ : DifferentiableAt ℝ Φ x)
    (ha0 : ‖a x‖ ≤ 1) (hβ0 : ‖β (T x)‖ ≤ 1) (hΦ0 : ‖Φ x‖ ≤ 1)
    (ha1 : ‖fderiv ℝ a x‖ ≤ A) (hβ1 : ‖fderiv ℝ β (T x)‖ ≤ D)
    (hT1 : ‖fderiv ℝ T x‖ ≤ P) (hΦ1 : ‖fderiv ℝ Φ x‖ ≤ Q) :
    ‖fderiv ℝ (fun y => c • (a y • (β (T y) • Φ y))) x‖ ≤
      |c| * (A + D * P + Q) := by
  have hA : 0 ≤ A := (norm_nonneg _).trans ha1
  have hD : 0 ≤ D := (norm_nonneg _).trans hβ1
  have hP : 0 ≤ P := (norm_nonneg _).trans hT1
  have hQ : 0 ≤ Q := (norm_nonneg _).trans hΦ1
  have hβT : DifferentiableAt ℝ (fun y => β (T y)) x := hβ.comp x hT
  have hβT1 : ‖fderiv ℝ (fun y => β (T y)) x‖ ≤ D * P :=
    (norm_fderiv_real_comp_le hβ hT).trans (mul_le_mul hβ1 hT1 (norm_nonneg _) hD)
  have hinner0 : ‖β (T x) • Φ x‖ ≤ 1 := by
    rw [norm_smul]
    nlinarith [norm_nonneg (β (T x)), norm_nonneg (Φ x)]
  have hinner1 : ‖fderiv ℝ (fun y => β (T y) • Φ y) x‖ ≤ Q + D * P := by
    calc
      _ ≤ ‖β (T x)‖ * ‖fderiv ℝ Φ x‖ +
          ‖fderiv ℝ (fun y => β (T y)) x‖ * ‖Φ x‖ :=
        norm_fderiv_real_smul_le hβT hΦ
      _ ≤ 1 * Q + (D * P) * 1 :=
        add_le_add (mul_le_mul hβ0 hΦ1 (norm_nonneg _) (by norm_num))
          (mul_le_mul hβT1 hΦ0 (norm_nonneg _) (mul_nonneg hD hP))
      _ = _ := by ring
  have houter : ‖fderiv ℝ (fun y => a y • (β (T y) • Φ y)) x‖ ≤ A + D * P + Q := by
    calc
      _ ≤ ‖a x‖ * ‖fderiv ℝ (fun y => β (T y) • Φ y) x‖ +
          ‖fderiv ℝ a x‖ * ‖β (T x) • Φ x‖ :=
        norm_fderiv_real_smul_le ha (hβT.smul hΦ)
      _ ≤ 1 * (Q + D * P) + A * 1 :=
        add_le_add (mul_le_mul ha0 hinner1 (norm_nonneg _) (by norm_num))
          (mul_le_mul ha1 hinner0 (norm_nonneg _) hA)
      _ = _ := by ring
  rw [fderiv_fun_const_smul (ha.fun_smul (hβT.fun_smul hΦ)) c, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left houter (abs_nonneg c)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in

theorem norm_prediction_product_le {a : E → ℝ} {β : ℝ → ℝ}
    {T : E → ℝ} {Φ : E → F} {x : E} (c : ℝ)
    (ha0 : ‖a x‖ ≤ 1) (hβ0 : ‖β (T x)‖ ≤ 1) (hΦ0 : ‖Φ x‖ ≤ 1) :
    ‖c • (a x • (β (T x) • Φ x))‖ ≤ |c| := by
  simp only [norm_smul, Real.norm_eq_abs]
  have hinner : |a x| * (|β (T x)| * ‖Φ x‖) ≤ 1 := by
    have ha0' : |a x| ≤ 1 := ha0
    have hβ0' : |β (T x)| ≤ 1 := hβ0
    calc
      _ ≤ 1 * (1 * 1) :=
        mul_le_mul ha0' (mul_le_mul hβ0' hΦ0 (norm_nonneg _) (by norm_num))
          (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (by norm_num)
      _ = 1 := by norm_num
  simpa using mul_le_mul_of_nonneg_left hinner (abs_nonneg c)

theorem norm_add_fderiv_prediction_product_le
    {a : E → ℝ} {β : ℝ → ℝ} {T : E → ℝ} {Φ : E → F} {x : E}
    {A D P Q : ℝ} (c : ℝ)
    (ha : DifferentiableAt ℝ a x) (hβ : DifferentiableAt ℝ β (T x))
    (hT : DifferentiableAt ℝ T x) (hΦ : DifferentiableAt ℝ Φ x)
    (ha0 : ‖a x‖ ≤ 1) (hβ0 : ‖β (T x)‖ ≤ 1) (hΦ0 : ‖Φ x‖ ≤ 1)
    (ha1 : ‖fderiv ℝ a x‖ ≤ A) (hβ1 : ‖fderiv ℝ β (T x)‖ ≤ D)
    (hT1 : ‖fderiv ℝ T x‖ ≤ P) (hΦ1 : ‖fderiv ℝ Φ x‖ ≤ Q) :
    ‖c • (a x • (β (T x) • Φ x))‖ +
      ‖fderiv ℝ (fun y => c • (a y • (β (T y) • Φ y))) x‖ ≤
      |c| * (1 + A + D * P + Q) := by
  calc
    _ ≤ |c| + |c| * (A + D * P + Q) :=
      add_le_add (norm_prediction_product_le c ha0 hβ0 hΦ0)
        (norm_fderiv_prediction_product_le c ha hβ hT hΦ ha0 hβ0 hΦ0 ha1 hβ1 hT1 hΦ1)
    _ = _ := by ring

lemma prediction_growth_absorb {A D K p k : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hK : 0 ≤ K) (hp : 0 ≤ p) (hk : 0 ≤ k) :
    1 + A + D * p + K * (1 + k) ≤ (1 + A + D + K) * (1 + p + k) := by
  have h1 : 0 ≤ p + k + A * p + A * k + D + D * k + K * p := by positivity
  nlinarith

theorem prediction_term_majorant
    {a : E → ℝ} {β : ℝ → ℝ} {T : E → ℝ} {Φ : E → F} {x : E}
    {A D B K : ℝ} (c : ℝ) (m : ℕ)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (ha : DifferentiableAt ℝ a x) (hβ : DifferentiableAt ℝ β (T x))
    (hT : DifferentiableAt ℝ T x) (hΦ : DifferentiableAt ℝ Φ x)
    (ha0 : ‖a x‖ ≤ 1) (hβ0 : ‖β (T x)‖ ≤ 1) (hΦ0 : ‖Φ x‖ ≤ 1)
    (ha1 : ‖fderiv ℝ a x‖ ≤ A) (hβ1 : ‖fderiv ℝ β (T x)‖ ≤ D)
    (hT1 : ‖fderiv ℝ T x‖ ≤ B ^ m)
    (hΦ1 : ‖fderiv ℝ Φ x‖ ≤ K * (1 + (2 : ℝ) ^ (m + 1))) :
    ‖c • (a x • (β (T x) • Φ x))‖ +
      ‖fderiv ℝ (fun y => c • (a y • (β (T y) • Φ y))) x‖ ≤
      (|c| * (1 + A + D + K)) * (1 + B ^ m + (2 : ℝ) ^ (m + 1)) := by
  calc
    _ ≤ |c| * (1 + A + D * B ^ m + K * (1 + (2 : ℝ) ^ (m + 1))) :=
      norm_add_fderiv_prediction_product_le c ha hβ hT hΦ ha0 hβ0 hΦ0 ha1 hβ1 hT1 hΦ1
    _ ≤ |c| * ((1 + A + D + K) * (1 + B ^ m + (2 : ℝ) ^ (m + 1))) :=
      mul_le_mul_of_nonneg_left
        (prediction_growth_absorb hA hD hK (pow_nonneg hB _) (by positivity))
        (abs_nonneg c)
    _ = _ := by ring

theorem contDiff_predictionTerm {n : WithTop ℕ∞} {α β : ℝ → ℝ}
    {t T : E → ℝ} {Φ : E → F} (c : ℝ)
    (hα : ContDiff ℝ n α) (hβ : ContDiff ℝ n β)
    (ht : ContDiff ℝ n t) (hT : ContDiff ℝ n T) (hΦ : ContDiff ℝ n Φ) :
    ContDiff ℝ n (predictionTerm c α β t T Φ) := by
  exact (((hα.comp ht).smul ((hβ.comp hT).smul hΦ)).const_smul c)

end Estimates

end Problem340

end

end OAI
