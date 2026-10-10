import OAI.Geometry.RCD.Coordinates.NormalizedJetStep
import OAI.Geometry.RCD.Metric.ScalarMetricBootstrap

namespace OAI

/-!
# Differential identities for the metric iteration

These identities concern the actual update `h + (Dh)⁻ᵀ v`. In particular,
the second derivative includes both mixed terms and the second derivative
of the inverse field. The metric identity keeps the diagonal cancellation
before taking norms.
-/

open Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The second derivative in one direction, expressed without choosing
coordinates on the space of bilinear maps. -/
def diagonalSecond (f : E → F) (x ξ : E) : F :=
  fderiv ℝ (fun y => fderiv ℝ f y ξ) x ξ

/-- Evaluating the derivative of a linear-map-valued function commutes
with evaluation on a fixed vector. -/
theorem fderiv_apply_fixed {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {A : E → F →L[ℝ] G} {x : E} (hA : DifferentiableAt ℝ A x) (u : E)
    (v : F) :
    fderiv ℝ (fun y => A y v) x u = fderiv ℝ A x u v := by
  have h := hA.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  simpa using congrArg (fun L => L u) h.fderiv

/-- The directional form is the diagonal evaluation of the genuine
second Fréchet derivative. -/
theorem diagonalSecond_eq {f : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (ξ : E) :
    diagonalSecond f x ξ = iteratedFDeriv ℝ 2 f x (fun _ => ξ) := by
  rw [diagonalSecond, iteratedFDeriv_two_apply]
  exact fderiv_apply_fixed ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)) ξ ξ

/-- All three terms of the second derivative of an operator applied to
a vector field, with the two equal mixed terms combined. -/
theorem diagonalSecond_clm_apply {K : E → F →L[ℝ] F} {v : E → F} {x : E}
    (hK : ContDiffAt ℝ 2 K x) (hv : ContDiffAt ℝ 2 v x) (ξ : E) :
    diagonalSecond (fun y => K y (v y)) x ξ =
      K x (diagonalSecond v x ξ) +
        2 • (fderiv ℝ K x ξ (fderiv ℝ v x ξ)) +
        diagonalSecond K x ξ (v x) := by
  have hKdiff := hK.differentiableAt (by norm_num)
  have hvdiff := hv.differentiableAt (by norm_num)
  have hdK := (hK.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdv := (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdKξ := hdK.hasFDerivAt.clm_apply (hasFDerivAt_const ξ x)
  have hdvξ := hdv.hasFDerivAt.clm_apply (hasFDerivAt_const ξ x)
  have hterm := (hKdiff.hasFDerivAt.clm_apply hdvξ).add
    (hdKξ.clm_apply hvdiff.hasFDerivAt)
  have heq : (fun y => K y (fderiv ℝ v y ξ) + fderiv ℝ K y ξ (v y)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ (fun z => K z (v z)) y ξ) := by
    filter_upwards [hK.eventually (by norm_num), hv.eventually (by norm_num)] with y hKy hvy
    rw [fderiv_clm_apply (hKy.differentiableAt (by norm_num))
      (hvy.differentiableAt (by norm_num))]
    simp
  have hder := hterm.congr_of_eventuallyEq heq.symm
  have hvsecond := fderiv_apply_fixed hdv ξ ξ
  have hKsecond := fderiv_apply_fixed hdK ξ ξ
  rw [diagonalSecond, hder.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply]
  dsimp [diagonalSecond] at hvsecond hKsecond ⊢
  rw [hvsecond, hKsecond]
  simp only [map_zero, zero_apply, zero_add]
  module

/-- Addition of maps preserves the actual second directional derivative. -/
theorem diagonalSecond_add {f g : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (ξ : E) :
    diagonalSecond (fun y => f y + g y) x ξ =
      diagonalSecond f x ξ + diagonalSecond g x ξ := by
  rw [diagonalSecond_eq (hf.add hg), diagonalSecond_eq hf, diagonalSecond_eq hg]
  rw [show (fun y => f y + g y) = f + g from rfl, iteratedFDeriv_add_apply hf hg]
  rfl

end General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The exact metric increment for the genuine update. The derivative
of the inverse transpose is contracted with the old Jacobian before
being estimated, so only the diagonal second derivative of `h` remains. -/
theorem inverseTranspose_update_metric_increment
    {h v : E → E} {x : E} (hh : ContDiffAt ℝ 2 h x)
    (hv : DifferentiableAt ℝ v x) (J : E ≃L[ℝ] E)
    (hJ : fderiv ℝ h x = (J : E →L[ℝ] E)) (ξ : E) :
    let next := fun y => h y + operatorInverseTranspose (fderiv ℝ h y) (v y)
    let delta := fderiv ℝ next x ξ - J ξ
    ‖fderiv ℝ next x ξ‖ ^ 2 - ‖J ξ‖ ^ 2 =
      2 * ⟪ξ, fderiv ℝ v x ξ⟫_ℝ -
        2 * ⟪diagonalSecond h x ξ, inverseTranspose J (v x)⟫_ℝ + ‖delta‖ ^ 2 := by
  dsimp only
  have hdJ := (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hi := hasFDerivAt_operator_inverseTranspose J
  rw [← hJ] at hi
  have hK := hi.comp x hdJ.hasFDerivAt
  have hstep := (hh.differentiableAt (by norm_num)).hasFDerivAt.fun_add
    (hK.clm_apply hv.hasFDerivAt)
  change HasFDerivAt (fun y => h y +
    operatorInverseTranspose (fderiv ℝ h y) (v y)) _ x at hstep
  have hder : fderiv ℝ (fun y => h y +
      operatorInverseTranspose (fderiv ℝ h y) (v y)) x ξ =
      J ξ + (inverseTranspose J (fderiv ℝ v x ξ) +
        inverseTransposeVariation J (fderiv ℝ (fderiv ℝ h) x ξ) (v x)) := by
    rw [hstep.fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, hJ]
    simp only [Function.comp_apply, hJ, operatorInverseTranspose_equiv]
    have hvar := inverseTranspose_derivative_apply J (fderiv ℝ (fderiv ℝ h) x ξ)
    simp only [ContinuousLinearMap.comp_apply] at hvar
    rw [hvar]
    rfl
  rw [hder]
  have hdiag : diagonalSecond h x ξ = fderiv ℝ (fderiv ℝ h) x ξ ξ :=
    fderiv_apply_fixed hdJ ξ ξ
  rw [hdiag]
  simpa only [add_sub_cancel_left] using
    norm_sq_inverseTranspose_increment J (fderiv ℝ (fderiv ℝ h) x ξ)
      ξ (fderiv ℝ v x ξ) (v x)

/-- The first two inverse-field costs follow from only three source
derivatives. The same constant works for every point and jet base. -/
theorem exists_inverseTranspose_low_order_cost {A : ℝ} (hA : 1 ≤ A) :
    ∃ C : ℝ, Real.sqrt A ≤ C ∧ 2 * A ≤ C ∧
      ∀ (B : ℝ), 0 < B → ∀ (h : E → E) (x : E),
      ContDiffAt ℝ 3 h x → IsUnit (fderiv ℝ h x) →
      ‖Ring.inverse (fderiv ℝ h x)‖ ≤ Real.sqrt A →
      (∀ m, 2 ≤ m → m ≤ 3 → ‖iteratedFDeriv ℝ m h x‖ ≤
        B ^ (m - 1) * (m.factorial : ℝ) ^ 3) →
      let K := fun y => operatorInverseTranspose (fderiv ℝ h y)
      ‖K x‖ ≤ C ∧ ∀ ξ w : E,
        ‖fderiv ℝ K x ξ w‖ ≤ 8 * C * B * ‖ξ‖ * ‖w‖ ∧
        ‖diagonalSecond K x ξ w‖ ≤ 216 * C * B ^ 2 * ‖ξ‖ ^ 2 * ‖w‖ := by
  obtain ⟨C, hC0, hC1, hbound⟩ :=
    inverseTranspose_iteratedFDeriv_finite_uniform_bound (E := E) hA
  refine ⟨C, hC0, hC1, ?_⟩
  intro B hB h x hh hunit hinv hsource
  let J := fderiv ℝ h
  let K := fun y => operatorInverseTranspose (J y)
  have hJ : ContDiffAt ℝ 2 J x := hh.fderiv_right (by norm_num)
  have hK : ContDiffAt ℝ 2 K x := contDiffAt_inverseTranspose_field hJ hunit
  have hJacobian (m : ℕ) (hm : 0 < m) (hm2 : m ≤ 2) :
      ‖iteratedFDeriv ℝ m J x‖ ≤ factorialMajorant m * jetCoefficientScale B m := by
    rw [norm_iteratedFDeriv_fderiv]
    calc
      _ ≤ B ^ ((m + 1) - 1) * ((m + 1).factorial : ℝ) ^ 3 :=
        hsource (m + 1) (by omega) (by omega)
      _ = _ := by
        simp only [Nat.add_sub_cancel]
        unfold factorialMajorant jetCoefficientScale
        rw [Nat.factorial_succ]
        push_cast
        ring
  have hKb := hbound B hB 2 J x hJ hunit hinv hJacobian
  have h0 : ‖K x‖ ≤ C := by
    simpa [factorialMajorant] using hKb 0 (by omega)
  have h1 : ‖fderiv ℝ K x‖ ≤ 8 * C * B := by
    have hb := hKb 1 (by omega)
    norm_num [factorialMajorant, jetCoefficientScale] at hb
    convert hb using 1; ring
  have h2 : ‖iteratedFDeriv ℝ 2 K x‖ ≤ 216 * C * B ^ 2 := by
    have hb := hKb 2 (by omega)
    norm_num [factorialMajorant, jetCoefficientScale] at hb
    convert hb using 1; ring
  refine ⟨h0, fun ξ w => ⟨?_, ?_⟩⟩
  · calc
      _ ≤ ‖fderiv ℝ K x ξ‖ * ‖w‖ := (fderiv ℝ K x ξ).le_opNorm w
      _ ≤ (‖fderiv ℝ K x‖ * ‖ξ‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right ((fderiv ℝ K x).le_opNorm ξ) (norm_nonneg _)
      _ ≤ _ := by gcongr
  · rw [diagonalSecond_eq hK]
    calc
      _ ≤ ‖iteratedFDeriv ℝ 2 K x (fun _ => ξ)‖ * ‖w‖ :=
        (iteratedFDeriv ℝ 2 K x (fun _ => ξ)).le_opNorm w
      _ ≤ (‖iteratedFDeriv ℝ 2 K x‖ * ‖ξ‖ ^ 2) * ‖w‖ := by
        gcongr
        simpa using (iteratedFDeriv ℝ 2 K x).le_opNorm (fun _ => ξ)
      _ ≤ _ := by gcongr

end RegularPointCoordinates

end

end OAI
