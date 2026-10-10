import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousYProduct

namespace OAI

/-! # Complex conjugation on the faithful homogeneous space -/

open MeasureTheory
open scoped SchwartzMap ComplexConjugate ZeroAtInfty

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousSchwartzConjugation : 𝓢(E, ℂ) →L[ℝ] 𝓢(E, ℂ) :=
  (SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (ContinuousLinearEquiv.neg ℝ))

@[simp] theorem homogeneousSchwartzConjugation_apply (ψ : 𝓢(E, ℂ)) (ξ : E) :
    homogeneousSchwartzConjugation ψ ξ = conj (ψ (-ξ)) := rfl

@[simp] theorem homogeneousSchwartzConjugation_involutive (ψ : 𝓢(E, ℂ)) :
    homogeneousSchwartzConjugation (homogeneousSchwartzConjugation ψ) = ψ := by
  apply SchwartzMap.ext
  intro ξ
  simp

theorem homogeneousSchwartzConjugation_energy (s : ℝ) (ψ : 𝓢(E, ℂ)) :
    homogeneousFrequencyEnergy s (homogeneousSchwartzConjugation ψ) =
      homogeneousFrequencyEnergy s ψ := by
  unfold homogeneousFrequencyEnergy
  simp only [homogeneousSchwartzConjugation_apply, Complex.norm_conj]
  simpa only [norm_neg] using
    (integral_neg_eq_self (fun ξ : E => ‖ξ‖ ^ (2 * s) * ‖ψ ξ‖ ^ 2) volume)

theorem homogeneousSchwartzConjugation_norm (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ : 𝓢(E, ℂ)) :
    ‖homogeneousFrequencyEmbedding a k ha ha1 hk (homogeneousSchwartzConjugation ψ)‖ =
      ‖homogeneousFrequencyEmbedding a k ha ha1 hk ψ‖ := by
  have h₁ := homogeneousFrequencyEmbedding_norm_sq a k ha ha1 hk
    (homogeneousSchwartzConjugation ψ)
  have h₂ := homogeneousFrequencyEmbedding_norm_sq a k ha ha1 hk ψ
  rw [homogeneousSchwartzConjugation_energy, homogeneousSchwartzConjugation_energy] at h₁
  nlinarith [norm_nonneg (homogeneousFrequencyEmbedding a k ha ha1 hk ψ),
    norm_nonneg (homogeneousFrequencyEmbedding a k ha ha1 hk (homogeneousSchwartzConjugation ψ))]

noncomputable def homogeneousConjugation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) : HomogeneousY a k →L[ℝ] HomogeneousY a k :=
  (((homogeneousFrequencyEmbedding a k ha ha1 hk).restrictScalars ℝ).comp
    homogeneousSchwartzConjugation).toLinearMap.extendOfNorm
      ((homogeneousFrequencyEmbedding a k ha ha1 hk).restrictScalars ℝ).toLinearMap

theorem homogeneousConjugation_on_Schwartz (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ : 𝓢(E, ℂ)) :
    homogeneousConjugation a k ha ha1 hk (homogeneousFrequencyEmbedding a k ha ha1 hk ψ) =
      homogeneousFrequencyEmbedding a k ha ha1 hk (homogeneousSchwartzConjugation ψ) := by
  apply LinearMap.extendOfNorm_eq
    (f := (((homogeneousFrequencyEmbedding a k ha ha1 hk).restrictScalars ℝ).comp
      homogeneousSchwartzConjugation).toLinearMap)
    (e := ((homogeneousFrequencyEmbedding a k ha ha1 hk).restrictScalars ℝ).toLinearMap)
    (homogeneousFrequencyEmbedding_dense a k ha ha1 hk)
  refine ⟨1, fun χ => ?_⟩
  change ‖homogeneousFrequencyEmbedding a k ha ha1 hk (homogeneousSchwartzConjugation χ)‖ ≤
    1 * ‖homogeneousFrequencyEmbedding a k ha ha1 hk χ‖
  rw [one_mul]
  exact (homogeneousSchwartzConjugation_norm a k ha ha1 hk χ).le

theorem homogeneousConjugation_norm_le (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) :
    ‖homogeneousConjugation a k ha ha1 hk f‖ ≤ ‖f‖ := by
  have h := LinearMap.norm_extendOfNorm_apply_le
    (f := (((homogeneousFrequencyEmbedding a k ha ha1 hk).restrictScalars ℝ).comp
      homogeneousSchwartzConjugation).toLinearMap)
    (e := ((homogeneousFrequencyEmbedding a k ha ha1 hk).restrictScalars ℝ).toLinearMap)
    (homogeneousFrequencyEmbedding_dense a k ha ha1 hk) 1
    (fun χ => by
      change ‖homogeneousFrequencyEmbedding a k ha ha1 hk (homogeneousSchwartzConjugation χ)‖ ≤
        1 * ‖homogeneousFrequencyEmbedding a k ha ha1 hk χ‖
      rw [one_mul]
      exact (homogeneousSchwartzConjugation_norm a k ha ha1 hk χ).le) f
  simpa only [homogeneousConjugation, one_mul] using h

@[simp] theorem homogeneousConjugation_involutive (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) :
    homogeneousConjugation a k ha ha1 hk (homogeneousConjugation a k ha ha1 hk f) = f := by
  let C := homogeneousConjugation a k ha ha1 hk
  have he := (homogeneousFrequencyEmbedding_dense a k ha ha1 hk).equalizer
    (C.continuous.comp C.continuous) continuous_id (by
      funext ψ
      change homogeneousConjugation a k ha ha1 hk
        (homogeneousConjugation a k ha ha1 hk (homogeneousFrequencyEmbedding a k ha ha1 hk ψ)) = _
      rw [homogeneousConjugation_on_Schwartz, homogeneousConjugation_on_Schwartz,
        homogeneousSchwartzConjugation_involutive]
      rfl)
  exact congrFun he f

@[simp] theorem homogeneousConjugation_norm (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) :
    ‖homogeneousConjugation a k ha ha1 hk f‖ = ‖f‖ := by
  apply le_antisymm (homogeneousConjugation_norm_le a k ha ha1 hk f)
  simpa only [homogeneousConjugation_involutive] using
    homogeneousConjugation_norm_le a k ha ha1 hk (homogeneousConjugation a k ha ha1 hk f)

theorem inverseRadianFourier_conjugate_reflect (f : E → ℂ) (y : E) :
    inverseRadianFourier (fun ξ => conj (f (-ξ))) y = conj (inverseRadianFourier f y) := by
  unfold inverseRadianFourier radianFourierIntegral
  rw [map_mul, Complex.conj_ofReal, ← integral_conj]
  have h := integral_neg_eq_self
    (fun ξ : E => Complex.exp ((-inner ℝ ξ (-y) : ℝ) * Complex.I) * conj (f (-ξ))) volume
  rw [← h]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [inner_neg_left, inner_neg_right, neg_neg, map_mul, ← Complex.exp_conj,
    Complex.conj_I, Complex.conj_ofReal]
  congr 2
  push_cast
  ring

/-- The real-linear isometry is ordinary pointwise complex conjugation. -/
theorem homogeneousConjugation_physical (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) (y : E) :
    homogeneousPhysicalCLM a k ha ha1 hk (homogeneousConjugation a k ha ha1 hk f) y =
      conj (homogeneousPhysicalCLM a k ha ha1 hk f y) := by
  let P := homogeneousPhysicalCLM a k ha ha1 hk
  have hev : Continuous (fun h : C₀(E, ℂ) => h y) :=
    (BoundedContinuousFunction.evalCLM ℂ y).continuous.comp
      ZeroAtInftyContinuousMap.isometry_toBCF.continuous
  have he := (homogeneousFrequencyEmbedding_dense a k ha ha1 hk).equalizer
    ((hev.comp P.continuous).comp (homogeneousConjugation a k ha ha1 hk).continuous)
    (Complex.continuous_conj.comp (hev.comp P.continuous)) (by
      funext ψ
      change homogeneousPhysicalCLM a k ha ha1 hk
        (homogeneousConjugation a k ha ha1 hk (homogeneousFrequencyEmbedding a k ha ha1 hk ψ)) y =
          conj (homogeneousPhysicalCLM a k ha ha1 hk (homogeneousFrequencyEmbedding a k ha ha1 hk ψ) y)
      rw [homogeneousConjugation_on_Schwartz, homogeneousPhysicalCLM_rawSchwartz,
        homogeneousPhysicalCLM_rawSchwartz]
      exact inverseRadianFourier_conjugate_reflect ψ y)
  exact congrFun he f

end DefocusingNLS

end OAI
