import Mathlib
import OAI.Geometry.PrescribedPotential.AnalyticSupport

namespace OAI

/-! Matrix Differential New. -/

noncomputable section
open Matrix Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
namespace MongeAmpere
variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

lemma contDiff_det : ContDiff ℂ ∞ (fun H : Mat => H.det) := by
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro j _
  exact contDiff_apply_apply ℂ ℂ (σ j) j

lemma differentiable_det : Differentiable ℂ (fun H : Mat => H.det) :=
  contDiff_det.differentiable (by simp)

lemma fderiv_det_apply (H K : Mat) (hH : IsUnit H.det) :
    fderiv ℂ (fun M : Mat => M.det) H K = H.det * (H⁻¹ * K).trace := by
  have hp : HasDerivAt (fun t : ℂ => H + t • K) K 0 := by
    convert! ((hasDerivAt_id (0 : ℂ)).smul_const K).const_add H using 1
    simp only [one_smul]
  have hf := (differentiable_det (H + (0 : ℂ) • K)).hasFDerivAt.comp_hasDerivAt 0 hp
  have hf' : HasDerivAt (fun t : ℂ => (H + t • K).det)
      (fderiv ℂ (fun M : Mat => M.det) H K) 0 := by
    convert! hf using 1
    simp only [zero_smul, add_zero]
    rfl
  exact hf'.unique (hasDerivAt_det_add_smul H K hH)

lemma real_fderiv_det_apply (H K : Mat) (hH : IsUnit H.det) :
    fderiv ℝ (fun M : Mat => M.det) H K = H.det * (H⁻¹ * K).trace := by
  have hd := ((differentiable_det H).hasFDerivAt.restrictScalars ℝ).fderiv
  have he := congrArg (fun L : Mat →L[ℝ] ℂ => L K) hd
  exact he.trans (fderiv_det_apply H K hH)

lemma contDiff_adjugate : ContDiff ℂ ∞ (fun H : Mat => H.adjugate) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.adjugate_apply]
  apply contDiff_det.comp
  apply contDiff_pi.mpr
  intro k
  apply contDiff_pi.mpr
  intro l
  by_cases hk : k = j
  · subst k
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne hk]
    exact contDiff_apply_apply ℂ ℂ k l

lemma differentiableAt_inv (H : Mat) (hH : H.det ≠ 0) :
    DifferentiableAt ℂ (fun M : Mat => M⁻¹) H := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact ((differentiable_det H).inv hH).smul
    (contDiff_adjugate.differentiable (by simp) H)

def matrixMulCLM : Mat →L[ℝ] Mat →L[ℝ] Mat :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => LinearMap.toContinuousLinearMap
        { toFun := fun N => M * N
          map_add' := fun N P => Matrix.mul_add M N P
          map_smul' := by intro c N; exact Matrix.mul_smul M c N }
      map_add' := by
        intro M N
        apply ContinuousLinearMap.ext
        intro P
        exact Matrix.add_mul M N P
      map_smul' := by
        intro c M
        apply ContinuousLinearMap.ext
        intro N
        exact Matrix.smul_mul c M N }

lemma real_fderiv_matrix_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f h : E → Mat} {x : E} (hf : DifferentiableAt ℝ f x)
    (hh : DifferentiableAt ℝ h x) (u : E) :
    fderiv ℝ (fun y => f y * h y) x u =
      f x * fderiv ℝ h x u + fderiv ℝ f x u * h x := by
  have he := (matrixMulCLM.hasFDerivAt_of_bilinear hf.hasFDerivAt hh.hasFDerivAt).fderiv
  exact congrArg (fun L : E →L[ℝ] Mat => L u) he

lemma real_fderiv_inv_apply (H K : Mat) (hH : IsUnit H.det) :
    fderiv ℝ (fun M : Mat => M⁻¹) H K = -(H⁻¹ * K * H⁻¹) := by
  have hi := (differentiableAt_inv H (isUnit_iff_ne_zero.mp hH)).restrictScalars ℝ
  have he : (fun M : Mat => M * M⁻¹) =ᶠ[nhds H] (fun _ => 1) := by
    filter_upwards [(isOpen_ne.preimage differentiable_det.continuous).mem_nhds
      (isUnit_iff_ne_zero.mp hH)] with M hM
    exact Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM)
  have hd := congrArg (fun L : Mat →L[ℝ] Mat => L K) he.fderiv_eq
  have hp := real_fderiv_matrix_mul (differentiableAt_id (𝕜 := ℝ)) hi K
  have hid : (fderiv ℝ (id : Mat → Mat) H) K = K :=
    congrArg (fun L : Mat →L[ℝ] Mat => L K) (fderiv_id (𝕜 := ℝ) (x := H))
  have hz : H * fderiv ℝ (fun M : Mat => M⁻¹) H K + K * H⁻¹ = 0 := by
    have hp' : (fderiv ℝ (fun M : Mat => M * M⁻¹) H) K =
        H * fderiv ℝ (fun M : Mat => M⁻¹) H K + K * H⁻¹ :=
      hp.trans (congrArg (fun N : Mat =>
        H * fderiv ℝ (fun M : Mat => M⁻¹) H K + N * H⁻¹) hid)
    have hc : fderiv ℝ (fun _ : Mat => (1 : Mat)) H = 0 := fderiv_const_apply _
    exact hp'.symm.trans (hd.trans (congrArg (fun L : Mat →L[ℝ] Mat => L K) hc))

  have hl := congrArg (fun M : Mat => H⁻¹ * M) hz
  rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hH,
    Matrix.one_mul, Matrix.mul_zero, ← Matrix.mul_assoc] at hl
  exact eq_neg_of_add_eq_zero_left hl

lemma fderiv_inv_apply (H K : Mat) (hH : IsUnit H.det) :
    fderiv ℂ (fun M : Mat => M⁻¹) H K = -(H⁻¹ * K * H⁻¹) := by
  have hd := ((differentiableAt_inv H (isUnit_iff_ne_zero.mp hH)).hasFDerivAt.restrictScalars ℝ).fderiv
  have he := congrArg (fun L : Mat →L[ℝ] Mat => L K) hd
  exact he.symm.trans (real_fderiv_inv_apply H K hH)

lemma contDiffAt_inv (H : Mat) (hH : H.det ≠ 0) :
    ContDiffAt ℂ ∞ (fun M : Mat => M⁻¹) H := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (contDiff_det.contDiffAt.inv hH).smul contDiff_adjugate.contDiffAt

def weightedInverse (H : Mat) : Mat := H.det • H⁻¹

lemma contDiffAt_weightedInverse (H : Mat) (hH : IsUnit H.det) :
    ContDiffAt ℂ ∞ weightedInverse H :=
  contDiff_det.contDiffAt.smul (contDiffAt_inv H (isUnit_iff_ne_zero.mp hH))

lemma differentiableAt_weightedInverse (H : Mat) (hH : IsUnit H.det) :
    DifferentiableAt ℂ weightedInverse H :=
  (differentiable_det H).smul (differentiableAt_inv H (isUnit_iff_ne_zero.mp hH))

lemma fderiv_weightedInverse_apply (H K : Mat) (hH : IsUnit H.det) :
    fderiv ℂ weightedInverse H K =
      H.det • ((H⁻¹ * K).trace • H⁻¹ - H⁻¹ * K * H⁻¹) := by
  have he := ((differentiable_det H).hasFDerivAt.smul
    (differentiableAt_inv H (isUnit_iff_ne_zero.mp hH)).hasFDerivAt).fderiv
  have he' := congrArg (fun L : Mat →L[ℂ] Mat => L K) he
  change fderiv ℂ weightedInverse H K =
    H.det • (fderiv ℂ (fun M : Mat => M⁻¹) H K) +
      (fderiv ℂ (fun M : Mat => M.det) H K) • H⁻¹ at he'
  rw [fderiv_det_apply H K hH, fderiv_inv_apply H K hH] at he'
  rw [he', smul_sub, smul_neg, mul_smul]
  abel

end MongeAmpere

end

end OAI
