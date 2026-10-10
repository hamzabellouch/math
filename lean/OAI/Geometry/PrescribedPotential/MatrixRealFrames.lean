import Mathlib
import OAI.Geometry.PrescribedPotential.BoundedNormalFrames
import OAI.Geometry.PrescribedPotential.GlobalSobolev
import OAI.Geometry.PrescribedPotential.MatrixHilbertCoordinates

namespace OAI

/-! Matrix Real Frames. -/

section

noncomputable section
open Set Filter Topology Matrix Finset
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace MetricSystem
open EllipticKernel FrozenPoisson HigherJet KaehlerCalculus
variable {n : ℕ}
local instance frameRealECIP : InnerProductSpace ℝ (EC n) := InnerProductSpace.rclikeToReal ℂ (EC n)

 def realMatrix (M : Mat n) : EC n →L[ℝ] EC n :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M).restrictScalars ℝ

lemma realMatrix_mul (M N : Mat n) : realMatrix (M*N) = (realMatrix M).comp (realMatrix N) := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (M*N) x = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) N x)
  rw [map_mul]
  rfl
lemma realMatrix_one : realMatrix (1 : Mat n) = ContinuousLinearMap.id ℝ (EC n) := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (1 : Mat n) x = x
  rw [map_one]
  rfl

lemma realMatrix_adjoint (M : Mat n) : (realMatrix M).adjoint = realMatrix Mᴴ := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  change (inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M y) x).re = (inner ℂ y (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) Mᴴ x)).re
  congr 1
  have he : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) Mᴴ = (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M).adjoint := map_star _ M
  rw [he,ContinuousLinearMap.adjoint_inner_right]

 def frame (C D : Mat n) (hCD : C*D=1) (hDC : D*C=1) : EC n ≃L[ℝ] EC n :=
  { toLinearEquiv :=
    { toFun := fun x => (1/2:ℝ) • realMatrix C x
      invFun := fun x => (2:ℝ) • realMatrix D x
      left_inv := by
        intro x
        have he := congrArg (fun L : EC n →L[ℝ] EC n => L x) (realMatrix_mul D C)
        rw [hDC,realMatrix_one] at he
        simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at he
        simp only [map_smul,smul_smul]
        rw [← he]
        norm_num
      right_inv := by
        intro x
        have he := congrArg (fun L : EC n →L[ℝ] EC n => L x) (realMatrix_mul C D)
        rw [hCD,realMatrix_one] at he
        simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at he
        simp only [map_smul,smul_smul]
        rw [← he]
        norm_num
      map_add' := by intro x y; simp only [map_add,smul_add]
      map_smul' := by intro c x; simp only [map_smul]; exact smul_comm _ _ _ }
    continuous_toFun := ((continuous_const (y := (1/2:ℝ))).smul (realMatrix C).continuous)
    continuous_invFun := ((continuous_const (y := (2:ℝ))).smul (realMatrix D).continuous) }

lemma frame_gram {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ (EC n))
    (M C D : Mat n) (hCD : C*D=1) (hDC : D*C=1) (hM : Cᴴ*M*C=1)
    (H : EC n →L[ℝ] EC n →L[ℝ] HM n) :
    principalBilinear e M⁻¹ H = ∑ i, H (frame C D hCD hDC (e i)) (frame C D hCD hDC (e i)) := by
  have hD : IsUnit D := ⟨⟨D,C,hDC,hCD⟩,rfl⟩
  have hC : IsUnit C := ⟨⟨C,D,hCD,hDC⟩,rfl⟩
  have hInv : M⁻¹ = C*Cᴴ := by
    rw [unnormalize_matrix hCD hM,Matrix.mul_inv_rev,← Matrix.conjTranspose_nonsing_inv]
    have hid : D⁻¹ = C := by
      calc
        D⁻¹ = D⁻¹*(D*C) := by rw [hDC,mul_one]
        _ = C := by rw [← mul_assoc,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hD),one_mul]
    rw [hid]
  let T : EC n →L[ℝ] EC n := (1/2:ℝ) • realMatrix Cᴴ
  have hT : T.adjoint = (1/2:ℝ) • realMatrix C := by
    dsimp [T]
    rw [map_smul,realMatrix_adjoint,Matrix.conjTranspose_conjTranspose]
  rw [principalBilinear_inv,principalApply_gram e (traceBilin M) T]
  · rw [hT]
    rfl
  · intro v
    have hfactor : M⁻¹ = star Cᴴ * Cᴴ := by
      change M⁻¹ = Cᴴᴴ*Cᴴ
      simpa only [Matrix.conjTranspose_conjTranspose] using hInv
    have htr : traceBilin M (rankOne v) = (1/4:ℝ)*‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) Cᴴ v‖^2 := by
      convert trace_rankOne_factor M Cᴴ hfactor v using 1
      congr 1
      ext x y
      simp only [rankOne,ContinuousLinearMap.smulRight_apply,_root_.smul_apply,realInner_apply,smul_eq_mul]
      change (inner ℂ v x).re*(inner ℂ v y).re = _
      simp only [PiLp.inner_apply,Complex.re_sum]
      rfl
    rw [htr]
    dsimp [T,realMatrix]
    simp only [_root_.smul_apply,norm_smul,Real.norm_eq_abs]
    norm_num
    ring

 def realMatrixLinear (n : ℕ) : Mat n →ₗ[ℝ] (EC n →L[ℝ] EC n) where
  toFun := realMatrix
  map_add' := by intro M N; ext x; simp [realMatrix]
  map_smul' := by
    intro c M
    apply ContinuousLinearMap.ext
    intro x
    change Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) (c • M) x = c • Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) M x
    rw [show c • M = (c:ℂ) • M from rfl,map_smul]
    rfl

lemma frame_uniform_bound (B : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ M D : Mat n,
    ‖M‖ ≤ B → ‖D‖ ≤ B → ∀ hMD hDM,
    ‖(frame M D hMD hDM).toContinuousLinearMap‖ ≤ C ∧
    ‖(frame M D hMD hDM).symm.toContinuousLinearMap‖ ≤ C := by
  have hcontinuous : Continuous (realMatrix (n := n)) := (realMatrixLinear n).continuous_of_finiteDimensional
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:Mat n) B).exists_bound_of_continuousOn hcontinuous.continuousOn
  refine ⟨2*max C 0,by positivity,fun M D hM hD hMD hDM => ?_⟩
  have hm : ‖realMatrix M‖ ≤ max C 0 := (hC M (by simpa using hM)).trans (le_max_left _ _)
  have hd : ‖realMatrix D‖ ≤ max C 0 := (hC D (by simpa using hD)).trans (le_max_left _ _)
  change ‖(1/2:ℝ) • realMatrix M‖ ≤ 2*max C 0 ∧ ‖(2:ℝ) • realMatrix D‖ ≤ 2*max C 0
  simp only [norm_smul,Real.norm_eq_abs]
  rw [abs_of_pos (by norm_num : 0 < (1/2:ℝ)),abs_of_pos (by norm_num : 0 < (2:ℝ))]
  constructor <;> nlinarith [norm_nonneg (realMatrix M)]
end MetricSystem

end
end

end OAI
