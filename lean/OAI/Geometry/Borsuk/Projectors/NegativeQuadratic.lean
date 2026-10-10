import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.MatrixCompression
import OAI.Geometry.Borsuk.SphereGeometry.HemisphereChart

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace Topology
open Filter Set
section NegativeQuadratic
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
def NegativeQuadratic (B : E →L[ℝ] E) : Prop := ∀ v, v ≠ 0 → ⟪v,B v⟫ < 0
omit [FiniteDimensional ℝ E] in
lemma negativeQuadratic_of_unit (B : E →L[ℝ] E)
    (h : ∀ v, ‖v‖ = 1 → ⟪v,B v⟫ < 0) : NegativeQuadratic B := by
  intro v hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hh := h (‖v‖⁻¹ • v) (by simp [norm_smul,norm_inv,hv])
  rw [map_smul,real_inner_smul_left,real_inner_smul_right] at hh
  by_contra hge
  exact not_lt_of_ge (mul_nonneg (inv_nonneg.mpr hn.le)
    (mul_nonneg (inv_nonneg.mpr hn.le) (le_of_not_gt hge))) hh
lemma negativeQuadratic_isOpen (B : X → E →L[ℝ] E) (hB : Continuous B) :
    IsOpen {x | NegativeQuadratic (B x)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hcont : Continuous (fun p : X × E => ⟪p.2,B p.1 p.2⟫) :=
    continuous_snd.inner ((hB.comp continuous_fst).clm_apply continuous_snd)
  have hev := (isCompact_sphere (0:E) 1).eventually_forall_of_forall_eventually
    (P := fun y v => ⟪v,B y v⟫ < 0) (x₀ := x) (fun v hv =>
      hcont.continuousAt.eventually_lt continuousAt_const
        (hx v (fun he => by simp [he] at hv)))
  filter_upwards [hev] with y hy
  exact negativeQuadratic_of_unit (B y) (fun v hv => hy v (by simpa using hv))
omit [FiniteDimensional ℝ E] in
lemma negativeQuadratic_pos_sub {B : E →L[ℝ] E} (hB : NegativeQuadratic B)
    {v : E} (hv : v ≠ 0) {lam : ℝ} (hl : 0 < lam) : 0 < ⟪v,lam • v - B v⟫ := by
  rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
  exact sub_pos.mpr ((hB v hv).trans_le (mul_nonneg hl.le (sq_nonneg _)))
end NegativeQuadratic
end BorsukNine

namespace BorsukNine
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section MatrixBlocks
variable {μ ν : Type*} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
local notation "W" => EuclideanSpace ℝ μ
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (𝕜 := ℝ)

omit [DecidableEq ν] in
lemma matrixEmbed_selfAdjoint (e : W →ₗᵢ[ℝ] E) {B : Matrix μ μ ℝ} (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (matrixEmbed e B) := by
  change ((isometryMatrix e) * B * (isometryMatrix e)ᴴ)ᴴ = _
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  rw [show Bᴴ = B from hB.star_eq]
  exact (Matrix.mul_assoc _ _ _).symm

omit [DecidableEq ν] in
lemma matrixCompress_selfAdjoint (e : W →ₗᵢ[ℝ] E) {A : M} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (matrixCompress e A) := by
  change ((isometryMatrix e)ᴴ * A * (isometryMatrix e))ᴴ = _
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  rw [show Aᴴ = A from hA.star_eq]
  exact (Matrix.mul_assoc _ _ _).symm

lemma matrixCompress_embed (e : W →ₗᵢ[ℝ] E) (B : Matrix μ μ ℝ) :
    matrixCompress e (matrixEmbed e B) = B := by
  change (isometryMatrix e)ᴴ * (isometryMatrix e * B * (isometryMatrix e)ᴴ) * isometryMatrix e = B
  calc
    _ = ((isometryMatrix e)ᴴ * isometryMatrix e) * B * ((isometryMatrix e)ᴴ * isometryMatrix e) := by
      simp only [Matrix.mul_assoc]
    _ = B := by rw [isometryMatrix_star_mul,Matrix.one_mul,Matrix.mul_one]

lemma isometryMatrix_star_action (e : W →ₗᵢ[ℝ] E) (v : E) :
    Matrix.toEuclideanLin (isometryMatrix e)ᴴ v = e.toContinuousLinearMap.adjoint v := by
  apply ext_inner_left ℝ
  intro x
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  change ⟪x,(Matrix.toEuclideanLin (isometryMatrix e)).adjoint v⟫ = _
  rw [LinearMap.adjoint_inner_right,isometryMatrix_action,ContinuousLinearMap.adjoint_inner_right]
  rfl

lemma matrixCompress_action (e : W →ₗᵢ[ℝ] E) (A : M) (v : W) :
    op (matrixCompress e A) v = e.toContinuousLinearMap.adjoint (op A (e v)) := by
  change Matrix.toEuclideanLin ((isometryMatrix e)ᴴ * A * isometryMatrix e) v = _
  rw [toEuclideanLin_mul,toEuclideanLin_mul]
  change Matrix.toEuclideanLin (isometryMatrix e)ᴴ (Matrix.toEuclideanLin A
    (Matrix.toEuclideanLin (isometryMatrix e) v)) = _
  rw [isometryMatrix_action,isometryMatrix_star_action]
  rfl

noncomputable def blockScalar (c : E) (A : M) : ℝ := ⟪c,op A c⟫
noncomputable def blockOff (c : E) (e : W →ₗᵢ[ℝ] E) (A : M) : W := e.toContinuousLinearMap.adjoint (op A c)
noncomputable def blockCorner (e : W →ₗᵢ[ℝ] E) (A : M) : M := matrixEmbed e (matrixCompress e A)

omit [DecidableEq ν] in
lemma blockCorner_selfAdjoint (e : W →ₗᵢ[ℝ] E) {A : M} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (blockCorner e A) := matrixEmbed_selfAdjoint e (matrixCompress_selfAdjoint e hA)
lemma blockCorner_kernel (e : W →ₗᵢ[ℝ] E) {c : E} (he : ∀ v, ⟪c,e v⟫ = 0) (A : M) :
    op (blockCorner e A) c = 0 := matrixEmbed_kernel e _ he
lemma blockCorner_of_kernel (e : W →ₗᵢ[ℝ] E) {c : E}
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u) {A : M} (hA : IsSelfAdjoint A) (hAc : op A c = 0) :
    blockCorner e A = A := by
  apply matrixEmbed_compress e hA
  rintro _ ⟨x,rfl⟩
  exact hes _ (matrix_image_orthogonal_kernel hA hAc x)

lemma block_data_zero (c : E) (e : W →ₗᵢ[ℝ] E) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : M} (hA : IsSelfAdjoint A) (ha : blockScalar c A = 0)
    (hb : blockOff c e A = 0) (hC : blockCorner e A = 0) : A = 0 := by
  have hAc : op A c = 0 := by
    have hd := frame_decomposition c e hc he hes (op A c)
    change e (blockOff c e A) = op A c - blockScalar c A • c at hd
    simpa only [hb,ha,map_zero,zero_smul,sub_zero] using hd.symm
  rw [blockCorner_of_kernel e hes hA hAc] at hC
  exact hC

lemma blockScalar_continuous (c : E) : Continuous (blockScalar c : M → ℝ) :=
  continuous_const.inner (((Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).clm_apply continuous_const)
omit [DecidableEq μ] in
lemma blockOff_continuous (c : E) (e : W →ₗᵢ[ℝ] E) : Continuous (blockOff c e : M → W) :=
  e.toContinuousLinearMap.adjoint.continuous.comp
    (((Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).clm_apply continuous_const)
omit [DecidableEq ν] in
lemma blockCorner_continuous (e : W →ₗᵢ[ℝ] E) : Continuous (blockCorner e : M → M) :=
  (matrixEmbed e).continuous_of_finiteDimensional.comp (matrixCompress e).continuous_of_finiteDimensional

lemma blockOff_eigenvector {c u : E} (e : W →ₗᵢ[ℝ] E) (hc : ‖c‖ = 1)
    (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {A : M} {lam : ℝ} (_hu : ‖u‖ = 1) (hcu : 0 < ⟪c,u⟫) (hAu : op A u = lam • u) :
    blockOff c e A = lam • hemisphereInverse c e u - op (matrixCompress e A) (hemisphereInverse c e u) := by
  let v := hemisphereInverse c e u
  have heq : c + e v = ⟪c,u⟫⁻¹ • u := by
    rw [show v = hemisphereInverse c e u from rfl,hemisphereInverse,map_smul,
      frame_decomposition c e hc he hes,smul_sub,smul_smul,inv_mul_cancel₀ (ne_of_gt hcu),one_smul]
    abel
  have hae : op A (c + e v) = lam • (c + e v) := by
    rw [heq,map_smul,hAu,smul_comm]
  have hb := congrArg e.toContinuousLinearMap.adjoint hae
  rw [map_add,map_add,map_smul,map_add,adjoint_normal c e he,zero_add] at hb
  rw [adjoint_isometry_apply,← matrixCompress_action] at hb
  exact eq_sub_iff_add_eq.mpr hb
end MatrixBlocks
end BorsukNine

end OAI
