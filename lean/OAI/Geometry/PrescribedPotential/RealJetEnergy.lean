import Mathlib
import OAI.Geometry.PrescribedPotential.HigherDirectionalJets

namespace OAI

/-! Real Jet Energy. -/

section

 
noncomputable section
open Set Filter Topology Finset
open scoped ContDiff
namespace HigherJet
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma dir_add {f g : E → F} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : E) :
    dir v (fun y => f y+g y) x = dir v f x+dir v g x := by
  exact congrArg (fun T : E →L[ℝ] F => T v) (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv

lemma dir_smul {f : E → F} {x : E} (hf : DifferentiableAt ℝ f x) (c : ℝ) (v : E) :
    dir v (fun y => c • f y) x = c • dir v f x := by
  exact congrArg (fun T : E →L[ℝ] F => T v) (hf.hasFDerivAt.const_smul c).fderiv

lemma dir_inner {f g : E → F} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : E) :
    dir v (fun y => inner ℝ (f y) (g y)) x =
      inner ℝ (f x) (dir v g x)+inner ℝ (dir v f x) (g x) :=
  fderiv_inner_apply ℝ hf hg v

lemma dir_norm_sq {f : E → F} {x : E} (hf : DifferentiableAt ℝ f x) (v : E) :
    dir v (fun y => ‖f y‖^2) x = 2*inner ℝ (f x) (dir v f x) := by
  simpa only [dir,smul_apply,ContinuousLinearMap.comp_apply,
    innerSL_apply_apply,two_smul,two_mul,add_apply] using congrArg (fun map : E →L[ℝ] ℝ => map v) hf.hasFDerivAt.norm_sq.fderiv

lemma dir_dir_norm_sq {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) {x : E} (hx : x ∈ U) (v : E) :
    dir v (dir v (fun y => ‖f y‖^2)) x =
      2*‖dir v f x‖^2+2*inner ℝ (f x) (dir v (dir v f) x) := by
  have he : dir v (fun y => ‖f y‖^2) =ᶠ[𝓝 x]
      (fun y => 2*inner ℝ (f y) (dir v f y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact dir_norm_sq ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)) v
  rw [dir_congr he]
  have hfa := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hda := ((dir_smoothOn hU hf v).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  change dir v (fun y => (2:ℝ) • inner ℝ (f y) (dir v f y)) x = _
  rw [dir_smul (hfa.inner ℝ hda),dir_inner hfa hda,real_inner_self_eq_norm_sq]
  simp only [smul_eq_mul]
  ring

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def frameLaplace (v : ι → E) (f : E → F) (x : E) : F := ∑ i, dir (v i) (dir (v i) f) x

def frameGradientSq (v : ι → E) (f : E → F) (x : E) : ℝ := ∑ i, ‖dir (v i) f x‖^2

lemma frameLaplace_norm_sq {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) {x : E} (hx : x ∈ U) (v : ι → E) :
    frameLaplace v (fun y => ‖f y‖^2) x =
      2*frameGradientSq v f x+2*inner ℝ (f x) (frameLaplace v f x) := by
  simp only [frameLaplace,dir_dir_norm_sq hU hf hx,Finset.sum_add_distrib,
    ← Finset.mul_sum,inner_sum,frameGradientSq]

lemma dir_sum (f : κ → E → F) {x : E} (hf : ∀ j, DifferentiableAt ℝ (f j) x) (v : E) :
    dir v (fun y => ∑ j, f j y) x = ∑ j, dir v (f j) x := by
  rw [show (fun y => ∑ j, f j y) = ∑ j, f j from by ext y; simp]
  simpa only [dir,Finset.sum_apply,_root_.sum_apply] using congrArg (fun map : E →L[ℝ] F => map v)
    ((HasFDerivAt.sum (u := Finset.univ) (fun j _ => (hf j).hasFDerivAt)).fderiv)

lemma frameLaplace_sum {U : Set E} (hU : IsOpen U) (f : κ → E → F)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) U) {x : E} (hx : x ∈ U) (v : ι → E) :
    frameLaplace v (fun y => ∑ j, f j y) x = ∑ j, frameLaplace v (f j) x := by
  have hd (i : ι) : dir (v i) (fun y => ∑ j, f j y) =ᶠ[𝓝 x]
      (fun y => ∑ j, dir (v i) (f j) y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact dir_sum f (fun j => ((hf j).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)) _
  simp only [frameLaplace,dir_congr (hd _),dir_sum _ (fun j =>
    ((dir_smoothOn hU (hf j) _).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
  exact Finset.sum_comm

def familyEnergy (f : κ → E → F) (x : E) : ℝ := ∑ j, ‖f j x‖^2

def familyDissipation (v : ι → E) (f : κ → E → F) (x : E) : ℝ :=
  ∑ j, frameGradientSq v (f j) x

lemma familyEnergy_smoothOn {U : Set E} {f : κ → E → F}
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) U) : ContDiffOn ℝ ∞ (familyEnergy f) U :=
  ContDiffOn.sum (fun j _ => (hf j).norm_sq (𝕜 := ℝ))

lemma familyEnergy_laplace {U : Set E} (hU : IsOpen U) {f : κ → E → F}
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) U) {x : E} (hx : x ∈ U) (v : ι → E) :
    frameLaplace v (familyEnergy f) x = 2*familyDissipation v f x+
      2*∑ j, inner ℝ (f j x) (frameLaplace v (f j) x) := by
  change frameLaplace v (fun y => ∑ j, ‖f j y‖^2) x = _
  rw [frameLaplace_sum hU _ (fun j => (hf j).norm_sq (𝕜 := ℝ)) hx]
  simp only [frameLaplace_norm_sq hU (hf _) hx,Finset.sum_add_distrib,
    ← Finset.mul_sum,familyDissipation]

lemma familyEnergy_gradient_bound {U : Set E} (hU : IsOpen U) {f : κ → E → F}
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) U) {x : E} (hx : x ∈ U) (v : ι → E) :
    frameGradientSq v (familyEnergy f) x ≤
      4*familyEnergy f x*familyDissipation v f x := by
  have he (i : ι) : dir (v i) (familyEnergy f) x =
      2*∑ j, inner ℝ (f j x) (dir (v i) (f j) x) := by
    change dir (v i) (fun y => ∑ j, ‖f j y‖^2) x = _
    rw [dir_sum _ (fun j =>
      (((hf j).norm_sq (𝕜 := ℝ)).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
    simp only [dir_norm_sq ((hf _).contDiffAt (hU.mem_nhds hx) |>.differentiableAt (by simp)),Finset.mul_sum]
  have hb (i : ι) : (∑ j, inner ℝ (f j x) (dir (v i) (f j) x))^2 ≤
      familyEnergy f x*(∑ j, ‖dir (v i) (f j) x‖^2) := by
    let a : PiLp 2 (fun _ : κ => F) := WithLp.toLp 2 (fun j => f j x)
    let b : PiLp 2 (fun _ : κ => F) := WithLp.toLp 2 (fun j => dir (v i) (f j) x)
    have hh := (sq_le_sq₀ (abs_nonneg (inner ℝ a b))
      (mul_nonneg (norm_nonneg a) (norm_nonneg b))).mpr (abs_real_inner_le_norm a b)
    simpa only [sq_abs,mul_pow,PiLp.inner_apply,PiLp.norm_sq_eq_of_L2,
      a,b,PiLp.toLp_apply,familyEnergy] using hh
  calc
    _ = ∑ i, 4*(∑ j, inner ℝ (f j x) (dir (v i) (f j) x))^2 := by
      simp only [frameGradientSq,he,Real.norm_eq_abs,sq_abs,mul_pow]; norm_num
    _ ≤ ∑ i, 4*familyEnergy f x*(∑ j, ‖dir (v i) (f j) x‖^2) := by
      exact Finset.sum_le_sum (fun i _ => by nlinarith only [hb i])
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      rfl
end HigherJet

end
end

end OAI
