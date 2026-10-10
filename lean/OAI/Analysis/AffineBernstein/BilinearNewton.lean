import Mathlib
import OAI.Analysis.AffineBernstein.AngularCofactor
import OAI.Analysis.AffineBernstein.SmoothParameter
import OAI.Analysis.AffineBernstein.NewtonField
import OAI.Analysis.AffineBernstein.SphereTensorCalculus

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open scoped Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bilinearOfMatrix (b : OrthonormalBasis ι ℝ E) (A : Matrix ι ι ℝ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i, ∑ j, A i j • (InnerProductSpace.toDual ℝ E (b i)).smulRight
    (InnerProductSpace.toDual ℝ E (b j))

omit [DecidableEq ι] in
lemma bilinearOfMatrix_apply (b : OrthonormalBasis ι ℝ E) (A : Matrix ι ι ℝ) (v w : E) :
    bilinearOfMatrix b A v w = ∑ i, ∑ j, A i j * inner ℝ (b i) v * inner ℝ (b j) w := by
  simp only [bilinearOfMatrix, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    InnerProductSpace.toDual_apply_apply, smul_eq_mul, mul_assoc]

lemma bilinearOfMatrix_basis (b : OrthonormalBasis ι ℝ E) (A : Matrix ι ι ℝ) (i j : ι) :
    bilinearOfMatrix b A (b i) (b j) = A i j := by
  rw [bilinearOfMatrix_apply]
  simp [orthonormal_iff_ite.mp b.orthonormal]

omit [DecidableEq ι] in
lemma bilinearOfMatrix_symm (b : OrthonormalBasis ι ℝ E) {A : Matrix ι ι ℝ}
    (hA : A.IsSymm) (v w : E) : bilinearOfMatrix b A v w = bilinearOfMatrix b A w v := by
  have hs (i j : ι) : A i j = A j i := congrFun (congrFun hA j) i
  simp only [bilinearOfMatrix_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hs]
  ring

omit [DecidableEq ι] in
lemma bilinearOfMatrix_radial (b : OrthonormalBasis ι ℝ E) {A : Matrix ι ι ℝ}
    (hA : A.IsSymm) {e : E} {c : ℝ}
    (he : A *ᵥ (fun i => inner ℝ (b i) e) = c • (fun i => inner ℝ (b i) e)) (v : E) :
    bilinearOfMatrix b A e v = c * inner ℝ e v := by
  have hs (i j : ι) : A i j = A j i := congrFun (congrFun hA j) i
  rw [bilinearOfMatrix_apply, Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  have hm (j : ι) : (∑ i, A i j * inner ℝ (b i) e) = c * inner ℝ (b j) e := by
    simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hs] using congrFun he j
  simp_rw [hm, mul_assoc]
  rw [← Finset.mul_sum]
  have hinner : (∑ j, inner ℝ (b j) e * inner ℝ (b j) v) = inner ℝ e v := by
    simpa only [real_inner_comm e] using b.sum_inner_mul_inner e v
  rw [hinner]

omit [DecidableEq ι] in
lemma contDiffAt_bilinearOfMatrix (b : OrthonormalBasis ι ℝ E)
    {M : E → Matrix ι ι ℝ} {x : E} (hM : ∀ i j, ContDiffAt ℝ ∞ (fun q => M q i j) x) :
    ContDiffAt ℝ ∞ (fun q => bilinearOfMatrix b (M q)) x := by
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    @NormedSpace.toIsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) _ _ _
  unfold bilinearOfMatrix
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => (hM i j).smul contDiffAt_const

lemma fderiv_bilinearOfMatrix_basis (b : OrthonormalBasis ι ℝ E)
    {M : E → Matrix ι ι ℝ} {x : E}
    (hM : DifferentiableAt ℝ (fun q => bilinearOfMatrix b (M q)) x) (i j : ι) (v : E) :
    fderiv ℝ (fun q => bilinearOfMatrix b (M q)) x v (b i) (b j) =
      fderiv ℝ (fun q => M q i j) x v := by
  have he : (fun q => bilinearOfMatrix b (M q) (b i) (b j)) = fun q => M q i j := by
    funext q; exact bilinearOfMatrix_basis b (M q) i j
  have hh := fderiv_bilinear_field hM (differentiableAt_const (b i))
    (differentiableAt_const (b j)) v
  rw [he] at hh
  simpa only [fderiv_const_apply, zero_apply, map_zero, zero_apply, add_zero] using hh.symm

lemma bilinearOfMatrix_field_divergence (b : OrthonormalBasis ι ℝ E)
    {M : E → Matrix ι ι ℝ} {x : E}
    (hM : DifferentiableAt ℝ (fun q => bilinearOfMatrix b (M q)) x)
    (hd : ∀ j, (∑ i, fderiv ℝ (fun q => M q i j) x (b i)) = 0) (v : E) :
    (∑ i, fderiv ℝ (fun q => bilinearOfMatrix b (M q)) x (b i) (b i) v) = 0 := by
  have hv (i : ι) : fderiv ℝ (fun q => bilinearOfMatrix b (M q)) x (b i) (b i) v =
      ∑ j, inner ℝ (b j) v * fderiv ℝ (fun q => M q i j) x (b i) := by
    conv_lhs => rw [← b.sum_repr' v]
    simp only [map_sum, map_smul, smul_eq_mul, fderiv_bilinearOfMatrix_basis b hM]
  simp_rw [hv]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hd, mul_zero]
  exact Finset.sum_const_zero

/- Full ambient Hessian in a constant orthonormal basis. -/
def basisHessian (b : OrthonormalBasis ι ℝ E) (H : E → ℝ) (x : E) : Matrix ι ι ℝ :=
  fun i j => fderiv ℝ (fderiv ℝ H) x (b i) (b j)

omit [CompleteSpace E] [DecidableEq ι] in
lemma contDiffAt_basisHessian (b : OrthonormalBasis ι ℝ E) {H : E → ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ H x) (i j : ι) : ContDiffAt ℝ ∞ (fun q => basisHessian b H q i j) x :=
  (((hH.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply
    contDiffAt_const).clm_apply contDiffAt_const

omit [CompleteSpace E] [DecidableEq ι] in
lemma basisHessian_isSymm (b : OrthonormalBasis ι ℝ E) {H : E → ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ H x) : (basisHessian b H x).IsSymm := by
  ext i j
  exact (hH.isSymmSndFDerivAt (by simp)).eq _ _

omit [CompleteSpace E] [DecidableEq ι] in
lemma fderiv_basisHessian (b : OrthonormalBasis ι ℝ E) {H : E → ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ H x) (i j : ι) (v : E) :
    fderiv ℝ (fun q => basisHessian b H q i j) x v =
      fderiv ℝ (fderiv ℝ (fderiv ℝ H)) x v (b i) (b j) := by
  have hh := fderiv_bilinear_field
    (((hH.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    (differentiableAt_const (b i)) (differentiableAt_const (b j)) v
  simpa only [fderiv_const_apply, zero_apply, map_zero, add_zero, basisHessian] using hh

omit [CompleteSpace E] [DecidableEq ι] in
lemma basisHessian_codazzi (b : OrthonormalBasis ι ℝ E) {H : E → ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ H x) (l j m : ι) :
    fderiv ℝ (fun q => basisHessian b H q l m) x (b j) =
      fderiv ℝ (fun q => basisHessian b H q l j) x (b m) := by
  rw [fderiv_basisHessian b hH, fderiv_basisHessian b hH]
  have hs := (hH.fderiv_right (m := ∞) (by simp)).isSymmSndFDerivAt
    (by simp)
  calc
    _ = fderiv ℝ (fderiv ℝ (fderiv ℝ H)) x (b l) (b j) (b m) :=
      congrArg (fun L : E →L[ℝ] ℝ => L (b m)) (hs.eq (b j) (b l))
    _ = fderiv ℝ (fderiv ℝ (fderiv ℝ H)) x (b l) (b m) (b j) :=
      third_derivative_swap_last hH _ _ _
    _ = _ := congrArg (fun L : E →L[ℝ] ℝ => L (b j)) (hs.eq (b l) (b m))

/- Global polynomial tensor whose tangential restriction is the angular cofactor. -/
def supportNewtonTensor (b : OrthonormalBasis ι ℝ E) (H : E → ℝ) (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ := bilinearOfMatrix b (newtonTensor (basisHessian b H x))

lemma contDiffAt_supportNewtonTensor (b : OrthonormalBasis ι ℝ E) {H : E → ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ H x) : ContDiffAt ℝ ∞ (supportNewtonTensor b H) x := by
  apply contDiffAt_bilinearOfMatrix b
  intro i j
  have hM : ContDiffAt ℝ ∞ (fun q => fun l m => basisHessian b H q l m) x :=
    contDiffAt_pi.mpr fun l => contDiffAt_pi.mpr fun m => contDiffAt_basisHessian b hH l m
  exact (contDiff_newtonTensor_entry i j).contDiffAt.comp x hM

lemma supportNewtonTensor_isSymm (b : OrthonormalBasis ι ℝ E) {H : E → ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ H x) (u v : E) :
    supportNewtonTensor b H x u v = supportNewtonTensor b H x v u :=
  bilinearOfMatrix_symm b (newtonTensor_isSymm (basisHessian_isSymm b hH)) u v

lemma supportNewtonTensor_flat_divergence (b : OrthonormalBasis ι ℝ E) {H : E → ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ H x) (v : E) :
    (∑ i, fderiv ℝ (supportNewtonTensor b H) x (b i) (b i) v) = 0 := by
  apply bilinearOfMatrix_field_divergence b
    ((contDiffAt_supportNewtonTensor b hH).differentiableAt (by simp))
  intro j
  apply newtonTensor_divergence_of_codazzi (basisHessian b H) x b
  · intro l m
    exact (contDiffAt_basisHessian b hH l m).differentiableAt (by simp)
  · exact basisHessian_codazzi b hH

lemma supportNewtonTensor_radial (b : OrthonormalBasis ι ℝ E) {H : E → ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ H x)
    (hr : ∀ v, fderiv ℝ (fderiv ℝ H) x v x = 0) :
    ∃ c : ℝ, ∀ v, supportNewtonTensor b H x x v = c * inner ℝ x v := by
  have hv : basisHessian b H x *ᵥ (fun i => inner ℝ (b i) x) = 0 := by
    ext i
    change (∑ j, basisHessian b H x i j * inner ℝ (b j) x) = 0
    have hh := congrArg (fderiv ℝ (fderiv ℝ H) x (b i)) (b.sum_repr' x)
    simp only [map_sum, map_smul, smul_eq_mul] at hh
    simpa only [basisHessian, mul_comm, hr] using hh
  obtain ⟨c, hc⟩ := newtonTensor_radial hv
  exact ⟨c, fun v => bilinearOfMatrix_radial b
    (newtonTensor_isSymm (basisHessian_isSymm b hH)) hc v⟩

/- The genuinely differentiated angular divergence identity for a smooth
one-homogeneous support extension. Its only analytic input is the actual
radial Hessian identity; flat Piola and both normal cancellations are proved. -/
theorem supportNewtonTensor_round_divergence (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) {H : E → ℝ} (hH : ContDiffOn ℝ ∞ H U)
    (hr : ∀ q ∈ U, ∀ v, fderiv ℝ (fderiv ℝ H) q v q = 0)
    {e v : E} (heU : e ∈ U) (he : inner ℝ e e = 1) (hv : inner ℝ e v = 0) :
    (∑ i, roundTensorDerivative (supportNewtonTensor b H) e
      (tangentProjection e (b i)) (tangentProjection e (b i)) v) = 0 := by
  have hHe := hH.contDiffAt (hU.mem_nhds heU)
  apply projected_tensor_divergence b
    ((contDiffAt_supportNewtonTensor b hHe).differentiableAt (by simp)) he hv
    (supportNewtonTensor_isSymm b hHe)
  · filter_upwards [hU.mem_nhds heU] with q hq
    obtain ⟨c, hc⟩ := supportNewtonTensor_radial b
      (hH.contDiffAt (hU.mem_nhds hq)) (hr q hq)
    intro w
    rw [hc, hc]
    ring
  · exact supportNewtonTensor_flat_divergence b hHe

end AffineBernstein
end

end OAI
