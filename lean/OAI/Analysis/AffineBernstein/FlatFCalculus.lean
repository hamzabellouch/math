import Mathlib
import OAI.Analysis.AffineBernstein.FlatLogEuler

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma dirDeriv_sub {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : E) :
    dirDeriv v (fun y => f y-g y) x = dirDeriv v f x-dirDeriv v g x := by
  change (fderiv ℝ (f-g) x) v = _
  rw [fderiv_sub hf hg]
  rfl

lemma second_dirDeriv_sub {W : Set E} (hW : IsOpen W) {f g : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g W)
    {x : E} (hx : x ∈ W) (v w : E) :
    dirDeriv v (dirDeriv w (fun y => f y-g y)) x =
      dirDeriv v (dirDeriv w f) x-dirDeriv v (dirDeriv w g) x := by
  have he : dirDeriv w (fun y => f y-g y) =ᶠ[𝓝 x]
      (fun y => dirDeriv w f y-dirDeriv w g y) := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact dirDeriv_sub ((hf.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp))
      ((hg.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)) w
  change fderiv ℝ (dirDeriv w (fun y => f y-g y)) x v = _
  rw [he.fderiv_eq]
  exact dirDeriv_sub ((contDiffAt_dirDeriv (hf.contDiffAt (hW.mem_nhds hx)) w).differentiableAt (by simp))
    ((contDiffAt_dirDeriv (hg.contDiffAt (hW.mem_nhds hx)) w).differentiableAt (by simp)) v

lemma flatInverseTrace_sub {W : Set E} (hW : IsOpen W) {f g : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g W)
    {x : E} (hx : x ∈ W) (A : Matrix ι ι ℝ) (v : ι → E) :
    flatInverseTrace A v (fun y => f y-g y) x =
      flatInverseTrace A v f x-flatInverseTrace A v g x := by
  unfold flatInverseTrace
  simp_rw [second_dirDeriv_sub hW hf hg hx,mul_sub]
  simp only [Finset.sum_sub_distrib]

lemma flatInversePair_symm (A : Matrix ι ι ℝ) (hA : A.IsSymm)
    (v : ι → E) (f g : E → ℝ) (x : E) :
    flatInversePair A v f g x = flatInversePair A v g f x := by
  have hi : A⁻¹.IsSymm := by rw [Matrix.IsSymm,Matrix.transpose_nonsing_inv,hA.eq]
  unfold flatInversePair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hi.apply i j]
  ring

lemma flatInversePair_sub_self {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (v : ι → E) :
    flatInversePair A v (fun y => f y-g y) (fun y => f y-g y) x =
      flatInversePair A v f f x - 2*flatInversePair A v g f x + flatInversePair A v g g x := by
  have he : flatInversePair A v (fun y => f y-g y) (fun y => f y-g y) x =
      flatInversePair A v f f x-flatInversePair A v f g x-
        flatInversePair A v g f x+flatInversePair A v g g x := by
    unfold flatInversePair
    simp_rw [dirDeriv_sub hf hg]
    simp only [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,flatInversePair_symm A hA v f g]
  ring

lemma flatInversePair_sub_right {f g h : E → ℝ} {x : E}
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x)
    (A : Matrix ι ι ℝ) (v : ι → E) :
    flatInversePair A v f (fun y => g y-h y) x =
      flatInversePair A v f g x-flatInversePair A v f h x := by
  unfold flatInversePair
  simp_rw [dirDeriv_sub hg hh,mul_sub]
  simp only [Finset.sum_sub_distrib]

lemma matrix_inverse_contraction_self {A : Matrix ι ι ℝ} (hA : A.det ≠ 0) :
    (∑ j, ∑ i, A⁻¹ i j * A j i) = Fintype.card ι := by
  rw [Finset.sum_comm]
  have he := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA)
  have ht := congrArg Matrix.trace he
  simpa [Matrix.trace,Matrix.diag,Matrix.mul_apply] using ht

lemma log_second_identity {W : Set E} (hW : IsOpen W) {φ : E → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ W) (hpos : ∀ y ∈ W, 0 < φ y)
    {x : E} (hx : x ∈ W) (v w : E) :
    dirDeriv v (dirDeriv w φ) x = φ x *
      (dirDeriv v (dirDeriv w (fun y => Real.log (φ y))) x +
        dirDeriv v (fun y => Real.log (φ y)) x * dirDeriv w (fun y => Real.log (φ y)) x) := by
  have hp : ContDiffOn ℝ ∞ (fun y => Real.log (φ y)) W :=
    hφ.log (fun y hy => ne_of_gt (hpos y hy))
  have he : (fun y => Real.exp (Real.log (φ y))) =ᶠ[𝓝 x] φ := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact Real.exp_log (hpos y hy)
  rw [← second_dirDeriv_congr he]
  have hh := second_dirDeriv_expMul hW hp hx 1 v w
  simpa only [one_mul,one_pow,Real.exp_log (hpos x hx)] using hh

lemma flat_log_hessian_trace {W : Set E} (hW : IsOpen W) {φ : E → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ W) (hpos : ∀ y ∈ W, 0 < φ y)
    {x : E} (hx : x ∈ W) (A : Matrix ι ι ℝ) (v : ι → E) :
    flatInverseTrace A v φ x = φ x *
      (flatInverseTrace A v (fun y => Real.log (φ y)) x +
        flatInversePair A v (fun y => Real.log (φ y)) (fun y => Real.log (φ y)) x) := by
  unfold flatInverseTrace flatInversePair
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [log_second_identity hW hφ hpos hx]
  ring

end AffineBernstein
end

end OAI
