import OAI.Probability.InvariantIsing.Fields.FieldFiniteCoordinates
import OAI.Probability.InvariantIsing.Fields.FieldGaussianPairDerivative

namespace OAI

/-! Normalized Gaussian differentiation for the finite vector of field
covariance coordinates and the spatial coordinate. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

variable {n : ℕ}

/-- Derivative of the unnormalized Gaussian weight. -/
def fieldFiniteWeightDifferential (U : (FieldCovariate n) → ℝ → ℝ)
    (DU : (FieldCovariate n) → ℝ → (FieldCovariate n) →L[ℝ] ℝ) (ζ : ℝ)
    (p : FieldCovariate n) (u : ℝ) : (FieldCovariate n) →L[ℝ] ℝ :=
  Real.exp (ζ * U p u) • (ζ • DU p u)

/-- Derivative of the weighted observable. -/
def fieldFiniteObservableDifferential (U A : (FieldCovariate n) → ℝ → ℝ)
    (DU DA : (FieldCovariate n) → ℝ → (FieldCovariate n) →L[ℝ] ℝ) (ζ : ℝ)
    (p : FieldCovariate n) (u : ℝ) : (FieldCovariate n) →L[ℝ] ℝ :=
  Real.exp (ζ * U p u) • (DA p u + (ζ * A p u) • DU p u)

lemma field_finite_tiltedFamily_hasFDerivAt
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U A : (FieldCovariate n) → ℝ → ℝ)
    (DU DA : (FieldCovariate n) → ℝ → (FieldCovariate n) →L[ℝ] ℝ)
    {p : FieldCovariate n} {S : Set (FieldCovariate n)} (hS : S ∈ 𝓝 p) (ζ : ℝ)
    (hU : ∀ q, Measurable (U q)) (hA : ∀ q, Measurable (A q))
    (hDU : AEStronglyMeasurable (DU p) μ) (hDA : AEStronglyMeasurable (DA p) μ)
    (hE : Integrable (fun u => Real.exp (ζ * U p u)) μ)
    (hEA : Integrable (fun u => Real.exp (ζ * U p u) * A p u) μ)
    (MD MN : ℝ → ℝ) (hMD : Integrable MD μ) (hMN : Integrable MN μ)
    (hDen : ∀ q ∈ S, ∀ u, ‖fieldFiniteWeightDifferential U DU ζ q u‖ ≤ MD u)
    (hNum : ∀ q ∈ S, ∀ u, ‖fieldFiniteObservableDifferential U A DU DA ζ q u‖ ≤ MN u)
    (dU : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => U r u) (DU q u) q)
    (dA : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => A r u) (DA q u) q) :
    let Z := ∫ u, Real.exp (ζ * U p u) ∂μ
    let N := ∫ u, Real.exp (ζ * U p u) * A p u ∂μ
    HasFDerivAt (fun q => ∫ u, A q u ∂μ.tilted (fun u => ζ * U q u))
      (Z⁻¹ • (∫ u, fieldFiniteObservableDifferential U A DU DA ζ p u ∂μ) -
        (N * (Z ^ 2)⁻¹) • (∫ u, fieldFiniteWeightDifferential U DU ζ p u ∂μ)) p := by
  let Z := ∫ u, Real.exp (ζ * U p u) ∂μ
  let N := ∫ u, Real.exp (ζ * U p u) * A p u ∂μ
  let DZ := ∫ u, fieldFiniteWeightDifferential U DU ζ p u ∂μ
  let DN := ∫ u, fieldFiniteObservableDifferential U A DU DA ζ p u ∂μ
  have hZD : HasFDerivAt (fun q => ∫ u, Real.exp (ζ * U q u) ∂μ) DZ p := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le hS
      (Eventually.of_forall fun q => ((hU q).const_mul ζ).exp.aestronglyMeasurable)
      hE (((hU p).const_mul ζ).exp.aestronglyMeasurable.smul (hDU.const_smul ζ))
      (ae_of_all _ fun u q hq => hDen q hq u) hMD
    exact ae_of_all _ fun u q hq => ((dU q hq u).const_mul ζ).exp
  have hND : HasFDerivAt (fun q => ∫ u, Real.exp (ζ * U q u) * A q u ∂μ) DN p := by
    have hDM : AEStronglyMeasurable (fieldFiniteObservableDifferential U A DU DA ζ p) μ :=
      ((hU p).const_mul ζ).exp.aestronglyMeasurable.smul
        (hDA.add (((hA p).const_mul ζ).aestronglyMeasurable.smul hDU))
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le hS
      (Eventually.of_forall fun q => (((hU q).const_mul ζ).exp.mul (hA q)).aestronglyMeasurable)
      hEA hDM (ae_of_all _ fun u q hq => hNum q hq u) hMN
    refine ae_of_all _ fun u q hq => ?_
    convert (((dU q hq u).const_mul ζ).exp).mul (dA q hq u) using 1
    apply ContinuousLinearMap.ext
    intro v
    simp only [fieldFiniteObservableDifferential, smul_apply,
      add_apply, smul_eq_mul]
    ring
  have hZ : Z ≠ 0 := (integral_exp_pos μ (U p) hE).ne'
  have hInv : HasFDerivAt (fun q => (∫ u, Real.exp (ζ * U q u) ∂μ)⁻¹)
      (-(Z ^ 2)⁻¹ • DZ) p := by
    convert (hasDerivAt_inv hZ).hasFDerivAt.comp p hZD using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro v
      simp only [smul_apply, ContinuousLinearMap.comp_apply,
        smul_eq_mul]
      change -(Z ^ 2)⁻¹ * DZ v = DZ v * -(Z ^ 2)⁻¹
      ring
  have hquot := hND.mul hInv
  have he : (fun q => ∫ u, A q u ∂μ.tilted (fun u => ζ * U q u)) =
      fun q => (∫ u, Real.exp (ζ * U q u) * A q u ∂μ) *
        (∫ u, Real.exp (ζ * U q u) ∂μ)⁻¹ := by
    funext q
    rw [integral_tilted_eq_div, div_eq_mul_inv]
  rw [he]
  convert hquot using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [sub_apply, smul_apply,
    add_apply, smul_eq_mul]
  change Z⁻¹ * DN v - N * (Z ^ 2)⁻¹ * DZ v =
    N * (-(Z ^ 2)⁻¹ * DZ v) + Z⁻¹ * DN v
  ring

lemma field_finite_tiltedFamily_covariance_hasFDerivAt
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U A : (FieldCovariate n) → ℝ → ℝ)
    (DU DA : (FieldCovariate n) → ℝ → (FieldCovariate n) →L[ℝ] ℝ)
    {p : FieldCovariate n} {S : Set (FieldCovariate n)} (hS : S ∈ 𝓝 p) (ζ : ℝ)
    (hU : ∀ q, Measurable (U q)) (hA : ∀ q, Measurable (A q))
    (hDU : AEStronglyMeasurable (DU p) μ) (hDA : AEStronglyMeasurable (DA p) μ)
    (hE : Integrable (fun u => Real.exp (ζ * U p u)) μ)
    (hEA : Integrable (fun u => Real.exp (ζ * U p u) * A p u) μ)
    (MD MN : ℝ → ℝ) (hMD : Integrable MD μ) (hMN : Integrable MN μ)
    (hDen : ∀ q ∈ S, ∀ u, ‖fieldFiniteWeightDifferential U DU ζ q u‖ ≤ MD u)
    (hNum : ∀ q ∈ S, ∀ u, ‖fieldFiniteObservableDifferential U A DU DA ζ q u‖ ≤ MN u)
    (dU : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => U r u) (DU q u) q)
    (dA : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => A r u) (DA q u) q) :
    HasFDerivAt (fun q => ∫ u, A q u ∂μ.tilted (fun u => ζ * U q u))
      ((∫ u, DA p u + (ζ * A p u) • DU p u
          ∂μ.tilted (fun u => ζ * U p u)) -
        (∫ u, A p u ∂μ.tilted (fun u => ζ * U p u)) •
          (∫ u, ζ • DU p u ∂μ.tilted (fun u => ζ * U p u))) p := by
  have h := field_finite_tiltedFamily_hasFDerivAt μ U A DU DA hS ζ hU hA hDU hDA
    hE hEA MD MN hMD hMN hDen hNum dU dA
  convert h using 1
  rw [field_tilted_integral_normalize, field_tilted_integral_normalize,
    field_tilted_integral_normalize]
  simp only [smul_eq_mul, fieldFiniteObservableDifferential, fieldFiniteWeightDifferential,
    pow_two, smul_smul]
  congr 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply, smul_eq_mul]
  ring

lemma field_finite_gaussianPair_hasFDerivAt
    (U A : (FieldCovariate n) → ℝ → ℝ)
    (DU DA : (FieldCovariate n) → ℝ → (FieldCovariate n) →L[ℝ] ℝ)
    {p : FieldCovariate n} {S : Set (FieldCovariate n)} (hS : S ∈ 𝓝 p) (hpS : p ∈ S)
    (ζ C L CA CD CE : ℝ) (hCA : 0 ≤ CA) (hCD : 0 ≤ CD) (_hCE : 0 ≤ CE)
    (hU : ∀ q, Measurable (U q)) (hA : ∀ q, Measurable (A q))
    (hDU : AEStronglyMeasurable (DU p) (gaussianReal 0 1))
    (hDA : AEStronglyMeasurable (DA p) (gaussianReal 0 1))
    (hExp : ∀ q ∈ S, ∀ u, Real.exp (ζ * U q u) ≤ Real.exp (C + L * |u|))
    (hAb : ∀ q ∈ S, ∀ u, |A q u| ≤ CA * (1 + |u|))
    (hDb : ∀ q ∈ S, ∀ u, ‖DU q u‖ ≤ CD * (1 + |u|))
    (hEb : ∀ q ∈ S, ∀ u, ‖DA q u‖ ≤ CE * (1 + |u|) ^ 2)
    (dU : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => U r u) (DU q u) q)
    (dA : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => A r u) (DA q u) q) :
    HasFDerivAt (fun q => ∫ u, A q u
      ∂(gaussianReal 0 1).tilted (fun u => ζ * U q u))
      ((∫ u, DA p u + (ζ * A p u) • DU p u
          ∂(gaussianReal 0 1).tilted (fun u => ζ * U p u)) -
        (∫ u, A p u ∂(gaussianReal 0 1).tilted (fun u => ζ * U p u)) •
          (∫ u, ζ • DU p u ∂(gaussianReal 0 1).tilted (fun u => ζ * U p u))) p := by
  let E : ℝ → ℝ := fun u => Real.exp (C + L * |u|) * (1 + |u|) ^ 2
  have hEi : Integrable E (gaussianReal 0 1) :=
    field_gaussian_quadratic_envelope_integrable C L
  have hE : Integrable (fun u => Real.exp (ζ * U p u)) (gaussianReal 0 1) := by
    apply hEi.mono' ((hU p).const_mul ζ).exp.aestronglyMeasurable
    refine ae_of_all _ fun u => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (hExp p hpS u).trans (le_mul_of_one_le_right (Real.exp_pos _).le (by
      nlinarith [abs_nonneg u]))
  have hEA : Integrable (fun u => Real.exp (ζ * U p u) * A p u)
      (gaussianReal 0 1) := by
    apply (hEi.const_mul CA).mono' (((hU p).const_mul ζ).exp.mul (hA p)).aestronglyMeasurable
    refine ae_of_all _ fun u => ?_
    change ‖Real.exp (ζ * U p u) * A p u‖ ≤ CA * E u
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (C + L * |u|) * (CA * (1 + |u|)) :=
        mul_le_mul (hExp p hpS u) (hAb p hpS u) (abs_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (C + L * |u|) * (CA * (1 + |u|) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) hCA) (Real.exp_pos _).le
      _ = CA * E u := by dsimp only [E]; ring
  apply field_finite_tiltedFamily_covariance_hasFDerivAt (gaussianReal 0 1) U A DU DA
    hS ζ hU hA hDU hDA hE hEA
    (fun u => (|ζ| * CD) * E u) (fun u => (CE + |ζ| * CA * CD) * E u)
    (hEi.const_mul _) (hEi.const_mul _)
  · intro q hq u
    rw [fieldFiniteWeightDifferential, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (C + L * |u|) * (|ζ| * (CD * (1 + |u|))) :=
        mul_le_mul (hExp q hq u)
          (mul_le_mul_of_nonneg_left (hDb q hq u) (abs_nonneg _))
          (by positivity) (Real.exp_pos _).le
      _ ≤ Real.exp (C + L * |u|) * (|ζ| * (CD * (1 + |u|) ^ 2)) := by
        gcongr
        exact field_mark_one_add_le_sq u
      _ = _ := by dsimp only [E]; ring
  · intro q hq u
    rw [fieldFiniteObservableDifferential, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hinner : ‖DA q u + (ζ * A q u) • DU q u‖ ≤
        (CE + |ζ| * CA * CD) * (1 + |u|) ^ 2 := by
      calc
        _ ≤ ‖DA q u‖ + ‖(ζ * A q u) • DU q u‖ := norm_add_le _ _
        _ = ‖DA q u‖ + |ζ| * |A q u| * ‖DU q u‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_mul]
        _ ≤ CE * (1 + |u|) ^ 2 + |ζ| * (CA * (1 + |u|)) * (CD * (1 + |u|)) := by
          gcongr
          · exact hEb q hq u
          · exact hAb q hq u
          · exact hDb q hq u
        _ = _ := by ring
    calc
      _ ≤ Real.exp (C + L * |u|) * ((CE + |ζ| * CA * CD) * (1 + |u|) ^ 2) :=
        mul_le_mul (hExp q hq u) hinner (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by dsimp only [E]; ring
  · exact dU
  · exact dA


lemma field_finite_average_hasFDerivAt_of_envelope
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U : (FieldCovariate n) → ℝ → ℝ) (D : (FieldCovariate n) → ℝ → (FieldCovariate n) →L[ℝ] ℝ)
    {p : FieldCovariate n} {S : Set (FieldCovariate n)} (hS : S ∈ 𝓝 p)
    (hU : ∀ q, Measurable (U q)) (hD : AEStronglyMeasurable (D p) μ)
    (hi : Integrable (U p) μ) (ζ : ℝ)
    (hExp : Integrable (fun u => Real.exp (ζ * U p u)) μ)
    (B E : ℝ → ℝ) (hBi : Integrable B μ)
    (hEBi : Integrable (fun u => E u * B u) μ)
    (hB : ∀ q ∈ S, ∀ u, ‖D q u‖ ≤ B u)
    (hE : ∀ q ∈ S, ∀ u, Real.exp (ζ * U q u) ≤ E u)
    (hd : ∀ q ∈ S, ∀ u, HasFDerivAt (fun s => U s u) (D q u) q) :
    HasFDerivAt (fun q => if ζ = 0 then ∫ u, U q u ∂μ
        else Real.log (∫ u, Real.exp (ζ * U q u) ∂μ) / ζ)
      (∫ u, D p u ∂μ.tilted (fun u => ζ * U p u)) p := by
  by_cases hζ : ζ = 0
  · subst ζ
    simp only [ite_true, zero_mul, tilted_const]
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le hS
      (Eventually.of_forall fun q => (hU q).aestronglyMeasurable) hi hD
      (ae_of_all _ fun u q hq => hB q hq u) hBi
      (ae_of_all _ fun u q hq => hd q hq u)
  · have hexp := hasFDerivAt_integral_of_dominated_of_fderiv_le hS
      (F := fun q u => Real.exp (ζ * U q u))
      (F' := fun q u => Real.exp (ζ * U q u) • (ζ • D q u))
      (Eventually.of_forall fun q => ((hU q).const_mul ζ).exp.aestronglyMeasurable)
      hExp (((hU p).const_mul ζ).exp.aestronglyMeasurable.smul (hD.const_smul ζ))
      (bound := fun u => |ζ| * (E u * B u))
      (ae_of_all _ fun u q hq => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          norm_smul, Real.norm_eq_abs]
        calc
          _ = |ζ| * (Real.exp (ζ * U q u) * ‖D q u‖) := by ring
          _ ≤ |ζ| * (E u * B u) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (hE q hq u) (hB q hq u) (norm_nonneg _)
                ((Real.exp_pos _).le.trans (hE q hq u))) (abs_nonneg ζ))
      (hEBi.const_mul |ζ|)
      (ae_of_all _ fun u q hq => ((hd q hq u).const_mul ζ).exp)
    have hp := IsingPerceptron.integral_exp_pos μ (U p) hExp
    have hraw : (∫ u, D p u ∂μ.tilted (fun u => ζ * U p u)) =
        (∫ u, Real.exp (ζ * U p u) ∂μ)⁻¹ •
          (∫ u, Real.exp (ζ * U p u) • D p u ∂μ) := by
      rw [integral_tilted, ← integral_smul]
      congr 1
      funext u
      rw [smul_smul]
      congr 1
      ring
    have hfactor : (∫ u, Real.exp (ζ * U p u) • (ζ • D p u) ∂μ) =
        ζ • (∫ u, Real.exp (ζ * U p u) • D p u ∂μ) := by
      rw [← integral_smul]
      congr 1
      funext u
      rw [smul_smul, smul_smul]
      congr 1
      ring
    convert (hexp.log hp.ne').const_mul ζ⁻¹ using 1
    · funext q
      simp only [hζ, ite_false]
      ring
    · rw [hraw, hfactor]
      simp only [smul_smul]
      congr 1
      field_simp


end InvariantIsing

end

end OAI
