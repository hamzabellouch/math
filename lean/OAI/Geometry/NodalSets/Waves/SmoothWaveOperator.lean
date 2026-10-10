import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import OAI.Geometry.NodalSets.Elliptic.SmoothBeamJet

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma coordPartial_add {f u : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (i : Fin 4) : coordPartial i (fun x ↦ f x + u x) =
      fun x ↦ coordPartial i f x + coordPartial i u x := by
  funext x
  unfold coordPartial
  rw [fderiv_fun_add (hf.differentiable (by simp) x) (hu.differentiable (by simp) x)]
  rfl

lemma coordPartial_mul {f u : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (i : Fin 4) : coordPartial i (fun x ↦ f x * u x) =
      fun x ↦ coordPartial i f x * u x + f x * coordPartial i u x := by
  funext x
  unfold coordPartial
  rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hu.differentiable (by simp) x)]
  simp [smul_eq_mul]
  ring

lemma coordPartial_const_mul {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (a : ℂ) (i : Fin 4) :
    coordPartial i (fun x ↦ a * f x) = fun x ↦ a * coordPartial i f x := by
  rw [coordPartial_mul contDiff_const hf]
  ext x
  simp [coordPartial]

lemma coordPartial_exp {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
    coordPartial i (fun x ↦ Complex.exp (f x)) =
      fun x ↦ coordPartial i f x * Complex.exp (f x) := by
  funext x
  unfold coordPartial
  rw [((hf.differentiable (by simp) x).hasFDerivAt.cexp).fderiv]
  simp [smul_eq_mul, mul_comm]

lemma coordPartial_twice_mul {f u : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u)
    (i j : Fin 4) : coordPartial i (coordPartial j (fun x ↦ f x * u x)) = fun x ↦
      coordPartial i (coordPartial j f) x * u x +
      coordPartial j f x * coordPartial i u x +
      coordPartial i f x * coordPartial j u x +
      f x * coordPartial i (coordPartial j u) x := by
  rw [coordPartial_mul hf hu j,
    coordPartial_add ((coordPartial_contDiff hf j).mul hu) (hf.mul (coordPartial_contDiff hu j)),
    coordPartial_mul (coordPartial_contDiff hf j) hu i,
    coordPartial_mul hf (coordPartial_contDiff hu j) i]
  ext x
  ring

theorem smoothSecondOrder_mul (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ)
    {f u : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u) (x : Coord) :
    smoothSecondOrder g b (fun z ↦ f z * u z) x =
      f x * smoothSecondOrder g b u x + u x * smoothSecondOrder g b f x +
      ∑ i, ∑ j, g i j x *
        (coordPartial i f x * coordPartial j u x + coordPartial j f x * coordPartial i u x) := by
  simp only [smoothSecondOrder]
  simp_rw [coordPartial_twice_mul hf hu]
  simp only [coordPartial_mul hf hu,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [mul_left_comm, mul_comm]
  ring

def waveExp (phi : Coord → ℂ) (N : ℝ) : Coord → ℂ :=
  fun x ↦ Complex.exp ((N : ℂ) * phi x)

lemma waveExp_contDiff {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi) (N : ℝ) :
    ContDiff ℝ ∞ (waveExp phi N) := (contDiff_const.mul hp).cexp

lemma coordPartial_waveExp {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi) (N : ℝ) (i : Fin 4) :
    coordPartial i (waveExp phi N) =
      fun x ↦ (N : ℂ) * coordPartial i phi x * waveExp phi N x := by
  unfold waveExp
  rw [coordPartial_exp (contDiff_const.mul hp), coordPartial_const_mul hp]

lemma coordPartial_twice_waveExp {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi)
    (N : ℝ) (i j : Fin 4) : coordPartial i (coordPartial j (waveExp phi N)) =
      fun x ↦ ((N : ℂ) * coordPartial i (coordPartial j phi) x +
        (N : ℂ) ^ 2 * coordPartial i phi x * coordPartial j phi x) * waveExp phi N x := by
  rw [coordPartial_waveExp hp N j,
    coordPartial_mul (contDiff_const.mul (coordPartial_contDiff hp j)) (waveExp_contDiff hp N) i,
    coordPartial_const_mul (coordPartial_contDiff hp j), coordPartial_waveExp hp N i]
  ext x
  ring

theorem smoothSecondOrder_waveExp (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) {phi : Coord → ℂ} (hp : ContDiff ℝ ∞ phi)
    (N : ℝ) (x : Coord) :
    smoothSecondOrder g b (waveExp phi N) x =
      ((N : ℂ) * smoothSecondOrder g b phi x +
        (N : ℂ) ^ 2 * (smoothEikonal g phi x - 4)) * waveExp phi N x := by
  simp only [smoothSecondOrder]
  simp_rw [coordPartial_twice_waveExp hp N]
  simp only [coordPartial_waveExp hp N, smoothEikonal, add_sub_cancel_right,
    mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib]
  simp only [mul_assoc, mul_left_comm]
  ring

lemma symmetric_cross_sum (G : Fin 4 → Fin 4 → ℂ) (hG : ∀ i j, G i j = G j i)
    (a q : Fin 4 → ℂ) :
    (∑ i, ∑ j, G i j * (a i * q j + a j * q i)) =
      ∑ i, (2 * ∑ j, G i j * q j) * a i := by
  have hs : (∑ i, ∑ j, G i j * a j * q i) = ∑ i, ∑ j, G i j * a i * q j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hG j i]
  calc
    _ = (∑ i, ∑ j, G i j * a i * q j) + (∑ i, ∑ j, G i j * a j * q i) := by
      simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib]
    _ = 2 * (∑ i, ∑ j, G i j * a i * q j) := by rw [hs]; ring
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem smooth_wave_residual_identity (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (hg : ∀ i j x, g i j x = g j i x)
    {phi a : Coord → ℂ} (hp : ContDiff ℝ ∞ phi) (ha : ContDiff ℝ ∞ a)
    (N : ℝ) (x : Coord) :
    smoothSecondOrder g b (fun z ↦ a z * waveExp phi N z) x +
        ((4 : ℂ) * (N : ℂ) ^ 2 + 6 * (N : ℂ)) * (a x * waveExp phi N x) =
      waveExp phi N x *
        ((N : ℂ) ^ 2 * smoothEikonal g phi x * a x +
          (N : ℂ) * smoothTransport (smoothBeamVector g phi) (smoothBeamScalar g b phi)
            (fun _ ↦ 0) a x + smoothSecondOrder g b a x) := by
  rw [smoothSecondOrder_mul g b ha (waveExp_contDiff hp N), smoothSecondOrder_waveExp g b hp,
    symmetric_cross_sum (fun i j ↦ g i j x) (fun i j ↦ hg i j x)]
  simp only [coordPartial_waveExp hp N, smoothTransport, smoothBeamVector, smoothBeamScalar,
    sub_zero]
  have he : (∑ i, (2 * ∑ j, g i j x * ((N : ℂ) * coordPartial j phi x * waveExp phi N x)) *
      coordPartial i a x) =
      (N : ℂ) * waveExp phi N x *
        (∑ i, (2 * ∑ j, g i j x * coordPartial j phi x) * coordPartial i a x) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  ring

end
end Yau.Jets

end OAI
