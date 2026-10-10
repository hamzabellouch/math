import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalSobolev
import OAI.Geometry.PrescribedPotential.RealJetEnergy

namespace OAI

/-! Real Frame Scalar. -/

section

 
noncomputable section
open Set Filter Topology Finset
open scoped ContDiff
namespace HigherJet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

def frameGradient (v : ι → E) (f : E → ℝ) (x : E) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => dir (v i) f x)

lemma norm_frameGradient_sq (v : ι → E) (f : E → ℝ) (x : E) :
    ‖frameGradient v f x‖^2 = frameGradientSq v f x := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

lemma dir_mul {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : E) :
    dir v (fun y => f y*g y) x = dir v f x*g x+f x*dir v g x := by
  have h := congrArg (fun T : E →L[ℝ] ℝ => T v) (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv
  change dir v (fun y => f y*g y) x = _ at h
  simp only [add_apply, smul_apply, smul_eq_mul] at h
  rw [h]
  simp only [dir]
  ring

omit [Fintype ι] in
lemma frameGradient_mul {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : ι → E) :
    frameGradient v (fun y => f y*g y) x =
      g x • frameGradient v f x+f x • frameGradient v g x := by
  ext i
  simp only [frameGradient,PiLp.add_apply,PiLp.smul_apply,PiLp.toLp_apply,smul_eq_mul,dir_mul hf hg]
  ring

omit [Fintype ι] in
lemma frameGradient_add {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : ι → E) :
    frameGradient v (fun y => f y+g y) x = frameGradient v f x+frameGradient v g x := by
  ext i
  exact dir_add hf hg _

omit [Fintype ι] in
lemma frameGradient_const (c : ℝ) (v : ι → E) (x : E) :
    frameGradient v (fun _ : E => c) x = 0 := by
  ext i
  simp [frameGradient,dir]

lemma frameLaplace_mul {U : Set E} (hU : IsOpen U) {f g : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : E} (hx : x ∈ U) (v : ι → E) :
    frameLaplace v (fun y => f y*g y) x =
      f x*frameLaplace v g x+g x*frameLaplace v f x+
      2*inner ℝ (frameGradient v f x) (frameGradient v g x) := by
  have hfa := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hga := (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have he (i : ι) : dir (v i) (fun y => f y*g y) =ᶠ[𝓝 x]
      (fun y => dir (v i) f y*g y+f y*dir (v i) g y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact dir_mul ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      ((hg.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)) _
  have hd (i : ι) : dir (v i) (dir (v i) (fun y => f y*g y)) x =
      f x*dir (v i) (dir (v i) g) x+g x*dir (v i) (dir (v i) f) x+
      2*(dir (v i) f x*dir (v i) g x) := by
    have hdf := ((dir_smoothOn hU hf (v i)).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hdg := ((dir_smoothOn hU hg (v i)).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    rw [dir_congr (he i),dir_add (f := fun y => dir (v i) f y*g y) (g := fun y => f y*dir (v i) g y)
      (hdf.mul hga) (hfa.mul hdg),dir_mul hdf hga,dir_mul hfa hdg]
    ring
  simp only [frameLaplace,hd,Finset.sum_add_distrib,← Finset.mul_sum,
    frameGradient,PiLp.inner_apply,RCLike.inner_apply,starRingEnd_apply,star_trivial]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma frameLaplace_add {U : Set E} (hU : IsOpen U) {f g : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : E} (hx : x ∈ U) (v : ι → E) :
    frameLaplace v (fun y => f y+g y) x = frameLaplace v f x+frameLaplace v g x := by
  have he (i : ι) : dir (v i) (fun y => f y+g y) =ᶠ[𝓝 x]
      (fun y => dir (v i) f y+dir (v i) g y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact dir_add ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      ((hg.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)) _
  simp only [frameLaplace,dir_congr (he _),dir_add
    (((dir_smoothOn hU hf _).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    (((dir_smoothOn hU hg _).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)),Finset.sum_add_distrib]

lemma frameLaplace_const (c : ℝ) (v : ι → E) (x : E) :
    frameLaplace v (fun _ : E => c) x = 0 := by
  have he (i : ι) : dir (v i) (fun _ : E => c) = fun _ => 0 := by
    ext y
    simp [dir]
  simp only [frameLaplace,he]
  apply Finset.sum_eq_zero
  intro i _
  exact congrArg (fun T : E →L[ℝ] ℝ => T (v i))
    (hasFDerivAt_const (x := x) (c := (0 : ℝ))).fderiv

omit [Fintype ι] in
lemma frameGradient_eq_zero_of_localMax {f : E → ℝ} {x : E} (h : IsLocalMax f x) (v : ι → E) :
    frameGradient v f x = 0 := by
  ext i
  simp [frameGradient,dir,h.fderiv_eq_zero]

lemma frameLaplace_nonpos_of_localMax {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (h : IsLocalMax f x) (v : ι → E) :
    frameLaplace v f x ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  rw [dir_dir hf]
  exact EllipticKernel.second_fderiv_nonpos_at_localMax hf h (v i)
end HigherJet

end
end

end OAI
