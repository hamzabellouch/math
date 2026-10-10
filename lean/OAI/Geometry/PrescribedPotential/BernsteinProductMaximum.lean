import Mathlib
import OAI.Geometry.PrescribedPotential.RealFrameScalar
import OAI.Geometry.PrescribedPotential.WirtingerCalculus

namespace OAI

/-! Bernstein Product Maximum. -/

section

 
noncomputable section
open Set Filter Topology Finset
open scoped ContDiff
namespace BernsteinEstimate
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma product_gradient_cross_identity {η a T : ℝ} (hη : η ≠ 0) (ha : a ≠ 0)
    (X Y Z : V) (h : (a*T) • X+(η*T) • Y+(η*a) • Z=0) :
    2*η*inner ℝ Y Z+2*a*inner ℝ X Z+2*T*inner ℝ X Y =
      -2*η*T/a*‖Y‖^2-2*a*T/η*‖X‖^2-2*T*inner ℝ X Y := by
  have hx := congrArg (fun W => inner ℝ X W) h
  have hy := congrArg (fun W => inner ℝ Y W) h
  simp only [inner_add_right,inner_smul_right,inner_zero_right,real_inner_self_eq_norm_sq] at hx hy
  rw [real_inner_comm X Y] at hy
  have hx' := congrArg (fun r : ℝ => 2*a*r) hx
  have hy' := congrArg (fun r : ℝ => 2*η*r) hy
  field_simp
  nlinarith only [hx',hy']
end BernsteinEstimate

namespace HigherJet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma quartic_test_at_max {U : Set E} (hU : IsOpen U) {η S T : E → ℝ}
    (hηs : ContDiffOn ℝ ∞ η U) (hSs : ContDiffOn ℝ ∞ S U) (hTs : ContDiffOn ℝ ∞ T U)
    {x : E} (hx : x ∈ U) (v : ι → E) (A : ℝ)
    (hηx : η x ≠ 0) (hax : A+S x ≠ 0)
    (hmax : IsLocalMax (fun y => η y*(A+S y)*T y) x) :
    η x*(A+S x)*frameLaplace v T x+η x*T x*frameLaplace v S x+
      (A+S x)*T x*frameLaplace v η x -
      2*η x*T x/(A+S x)*‖frameGradient v S x‖^2 -
      2*(A+S x)*T x/η x*‖frameGradient v η x‖^2 -
      2*T x*inner ℝ (frameGradient v η x) (frameGradient v S x) ≤ 0 := by
  let a : E → ℝ := fun y => A+S y
  have has : ContDiffOn ℝ ∞ a U := contDiffOn_const.add hSs
  have hηa := (hηs.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hSa := (hSs.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hTa := (hTs.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have haa := (has.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hg : frameGradient v a x = frameGradient v S x := by
    rw [show a = fun y => A+S y from rfl,frameGradient_add (differentiableAt_const A) hSa,frameGradient_const,zero_add]
  have hl : frameLaplace v a x = frameLaplace v S x := by
    rw [show a = fun y => A+S y from rfl,frameLaplace_add hU contDiffOn_const hSs hx,frameLaplace_const,zero_add]
  have hgrad := frameGradient_eq_zero_of_localMax hmax v
  have hm := frameLaplace_nonpos_of_localMax
    (((hηs.mul has).mul hTs).contDiffAt (hU.mem_nhds hx)) hmax v
  change frameGradient v (fun y => (η y*a y)*T y) x = 0 at hgrad
  rw [frameGradient_mul (f := fun y => η y*a y) (hηa.mul haa) hTa,
    frameGradient_mul hηa haa,hg,smul_add,smul_smul,smul_smul] at hgrad
  have hcross := BernsteinEstimate.product_gradient_cross_identity (T := T x) hηx hax
    (frameGradient v η x) (frameGradient v S x) (frameGradient v T x)
    (by simpa only [mul_comm,mul_left_comm,mul_assoc,a] using hgrad)
  change frameLaplace v (fun y => (η y*a y)*T y) x ≤ 0 at hm
  rw [frameLaplace_mul hU (f := fun y => η y*a y) (hηs.mul has) hTs hx,
    frameLaplace_mul hU hηs has hx,frameGradient_mul hηa haa,hg,hl,
    inner_add_left,inner_smul_left,inner_smul_left] at hm
  dsimp only [a] at hm
  simp only [starRingEnd_apply,star_trivial] at hm
  simp only [neg_mul,neg_div] at hcross
  nlinarith only [hm,hcross]
end HigherJet

end
end

end OAI
