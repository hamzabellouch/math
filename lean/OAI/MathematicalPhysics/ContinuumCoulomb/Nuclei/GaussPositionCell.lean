import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.GaussTensorError
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.DirectionalFourthDerivative

namespace OAI

/-! The actual eight equal masses on any translated cube, with a fourth-order
error bound from the ambient fourth Fréchet derivative. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def cubePoint (b : Position) (d x y z : ℝ) : Position :=
  b + x • (d • EuclideanSpace.single 0 1) +
    y • (d • EuclideanSpace.single 1 1) + z • (d • EuclideanSpace.single 2 1)

def positionCellGauss (b : Position) (h : ℝ) (f : Position → ℝ) : ℝ :=
  (h/2)^3 * gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint
    (fun z => f (cubePoint b (h/2) x y z))))

def positionCellIntegral (b : Position) (h : ℝ) (f : Position → ℝ) : ℝ :=
  (h/2)^3 * (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1,
    f (cubePoint b (h/2) x y z))

theorem cubePoint_contDiff (b : Position) (d : ℝ) :
    ContDiff ℝ 4 (fun p : ℝ × ℝ × ℝ => cubePoint b d p.1 p.2.1 p.2.2) := by
  unfold cubePoint
  fun_prop

private theorem fourthDerivWithin_line_bound (f : Position → ℝ) (b v : Position) (t : ℝ)
    (hf : ContDiffAt ℝ 4 f (b+t • v)) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    ‖iteratedDerivWithin 4 (fun s : ℝ => f (b+s • v)) (Set.Icc (-1) 1) t‖ ≤
      ‖iteratedFDeriv ℝ 4 f (b+t • v)‖*‖v‖^4 := by
  have hline : ContDiffAt ℝ 4 (fun s : ℝ => f (b+s • v)) t :=
    hf.comp t (show ContDiffAt ℝ 4 (fun s : ℝ => b+s • v) t by fun_prop)
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    hline ht,Real.norm_eq_abs]
  exact fourthDeriv_affine_line_bound f b v t hf

private theorem cube_axis_fourth_bound (f : Position → ℝ) (b v : Position) (t d C : ℝ)
    (hf : ContDiffAt ℝ 4 f (b+t • v)) (ht : t ∈ Set.Icc (-1:ℝ) 1)
    (hD : ‖iteratedFDeriv ℝ 4 f (b+t • v)‖ ≤ C) (hv : ‖v‖ = d) :
    ‖iteratedDerivWithin 4 (fun s : ℝ => f (b+s • v)) (Set.Icc (-1) 1) t‖ ≤ C*d^4 := by
  apply (fourthDerivWithin_line_bound f b v t hf ht).trans
  rw [hv]
  exact mul_le_mul_of_nonneg_right hD (pow_nonneg (norm_nonneg v |>.trans_eq hv) _)

/-- A translated cell incurs at most `C*h^7`, so summing cell volumes leaves
an `h^4` global error. -/
theorem positionCellGauss_error (f : Position → ℝ) (hf : ContDiff ℝ 4 f)
    (b : Position) {h C : ℝ} (hh : 0 ≤ h) (hC : 0 ≤ C)
    (hD : ∀ x ∈ Set.Icc (-1:ℝ) 1, ∀ y ∈ Set.Icc (-1:ℝ) 1,
      ∀ z ∈ Set.Icc (-1:ℝ) 1,
      ‖iteratedFDeriv ℝ 4 f (cubePoint b (h/2) x y z)‖ ≤ C) :
    |positionCellGauss b h f-positionCellIntegral b h f| ≤ C*h^7 := by
  let d := h/2
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hv (i : Fin 3) : ‖d • (EuclideanSpace.single i 1 : Position)‖ = d := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd,PiLp.norm_single]
    norm_num
  have hxline (x y z : ℝ) : cubePoint b d x y z =
      (b+y • (d • EuclideanSpace.single 1 1)+z • (d • EuclideanSpace.single 2 1))+
      x • (d • EuclideanSpace.single 0 1) := by unfold cubePoint; module
  have hyline (x y z : ℝ) : cubePoint b d x y z =
      (b+x • (d • EuclideanSpace.single 0 1)+z • (d • EuclideanSpace.single 2 1))+
      y • (d • EuclideanSpace.single 1 1) := by unfold cubePoint; module
  have hzline (x y z : ℝ) : cubePoint b d x y z =
      (b+x • (d • EuclideanSpace.single 0 1)+y • (d • EuclideanSpace.single 1 1))+
      z • (d • EuclideanSpace.single 2 1) := rfl
  have hc : Continuous (fun p : ℝ × ℝ × ℝ => f (cubePoint b d p.1 p.2.1 p.2.2)) :=
    hf.continuous.comp (cubePoint_contDiff b d).continuous
  have hfx (y z : ℝ) : ContDiff ℝ 4 (fun x => f (cubePoint b d x y z)) := by
    apply hf.comp
    unfold cubePoint
    fun_prop
  have hfy (x z : ℝ) : ContDiff ℝ 4 (fun y => f (cubePoint b d x y z)) := by
    apply hf.comp
    unfold cubePoint
    fun_prop
  have hfz (x y : ℝ) : ContDiff ℝ 4 (fun z => f (cubePoint b d x y z)) := by
    apply hf.comp
    unfold cubePoint
    fun_prop
  have hDx (y : ℝ) (hy : y ∈ Set.Icc (-1:ℝ) 1) (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1)
      (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) :
      ‖iteratedDerivWithin 4 (fun x => f (cubePoint b d x y z)) (Set.Icc (-1) 1) x‖ ≤ C*d^4 := by
    simp_rw [hxline]
    exact cube_axis_fourth_bound f _ _ x d C hf.contDiffAt hx
      (by rw [← hxline]; exact hD x hx y hy z hz) (hv 0)
  have hDy (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1)
      (y : ℝ) (hy : y ∈ Set.Icc (-1:ℝ) 1) :
      ‖iteratedDerivWithin 4 (fun y => f (cubePoint b d x y z)) (Set.Icc (-1) 1) y‖ ≤ C*d^4 := by
    simp_rw [hyline]
    exact cube_axis_fourth_bound f _ _ y d C hf.contDiffAt hy
      (by rw [← hyline]; exact hD x hx y hy z hz) (hv 1)
  have hDz (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) (y : ℝ) (hy : y ∈ Set.Icc (-1:ℝ) 1)
      (z : ℝ) (hz : z ∈ Set.Icc (-1:ℝ) 1) :
      ‖iteratedDerivWithin 4 (fun z => f (cubePoint b d x y z)) (Set.Icc (-1) 1) z‖ ≤ C*d^4 := by
    simp_rw [hzline]
    exact cube_axis_fourth_bound f _ _ z d C hf.contDiffAt hz
      (by rw [← hzline]; exact hD x hx y hy z hz) (hv 2)
  have he := gaussTensor3_C4_error (fun x y z => f (cubePoint b d x y z)) hc
    (mul_nonneg hC (pow_nonneg hd 4))
    (fun y _ z _ => (hfx y z).contDiffOn)
    (fun x _ z _ => (hfy x z).contDiffOn)
    (fun x _ y _ => (hfz x y).contDiffOn) hDx hDy hDz
  change |d^3*_ - d^3*_| ≤ _
  rw [← mul_sub,abs_mul,abs_of_nonneg (pow_nonneg hd 3)]
  apply (mul_le_mul_of_nonneg_left he (pow_nonneg hd 3)).trans_eq
  dsimp [d]
  ring

end ContinuumCoulomb

end

end OAI
