import Mathlib
import OAI.Geometry.SmoothYau.Geometry.PlanarTangentSurjective

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
open Set Filter
open scoped Topology ContDiff ComplexConjugate

def powerRadiusMap (n : ℕ) (z : ℂ) : ℝ × ℝ := ((z^n).re, Complex.normSq z)
lemma powerRadiusMap_contDiff (n : ℕ) : ContDiff ℝ ∞ (powerRadiusMap n) := by
  unfold powerRadiusMap
  apply ContDiff.prodMk
  · exact Complex.reCLM.contDiff.comp (contDiff_id.pow n)
  · change ContDiff ℝ ∞ (fun z : ℂ => z.re*z.re + z.im*z.im)
    exact
      (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
        (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
lemma powerRadiusMap_directional (n : ℕ) (z v : ℂ) :
    fderiv ℝ (powerRadiusMap n) z v =
      (((n:ℂ)*z^(n-1)*v).re, 2*(z.re*v.re + z.im*v.im)) := by
  have hp : HasFDerivAt (fun w : ℂ => w^n)
      (((n:ℂ)*z^(n-1)) • (ContinuousLinearMap.id ℝ ℂ)) z := by
    simpa using ((hasFDerivAt_id z).pow n)
  have hr := Complex.reCLM.hasFDerivAt.comp z hp
  have hn : HasFDerivAt (fun w : ℂ => Complex.normSq w)
      (2 • ((z.re • Complex.reCLM) + (z.im • Complex.imCLM))) z := by
    have h := ((Complex.reCLM.hasFDerivAt (x:=z)).mul Complex.reCLM.hasFDerivAt).add
      (Complex.imCLM.hasFDerivAt.mul Complex.imCLM.hasFDerivAt)
    have he : 2 • ((z.re • Complex.reCLM) + (z.im • Complex.imCLM)) =
        z.re • Complex.reCLM + z.re • Complex.reCLM +
          (z.im • Complex.imCLM + z.im • Complex.imCLM) := by
      ext w
      simp only [smul_apply, add_apply, smul_eq_mul,
        Complex.reCLM_apply,Complex.imCLM_apply]
      ring
    rw [he]
    exact h
  have h : HasFDerivAt (fun w : ℂ => ((w^n).re,Complex.normSq w))
      ((Complex.reCLM.comp (((n:ℂ)*z^(n-1)) • ContinuousLinearMap.id ℝ ℂ)).prod
        (2 • ((z.re • Complex.reCLM) + (z.im • Complex.imCLM)))) z :=
    hr.prodMk hn
  change fderiv ℝ (fun w : ℂ => ((w^n).re,Complex.normSq w)) z v = _
  rw [h.fderiv]
  simp [ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,smul_eq_mul]
  ring

theorem powerRadiusMap_surjective (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : (z^n).im ≠ 0) :
    Function.Surjective (fderiv ℝ (powerRadiusMap n) z) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hz0 : z ≠ 0 := by
    intro he
    simp only [he,zero_pow (show n ≠ 0 by omega),Complex.zero_im] at hz
    exact hz rfl
  have hR : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz0).ne'
  have hrad : fderiv ℝ (powerRadiusMap n) z z =
      ((n:ℝ)*(z^n).re,2*Complex.normSq z) := by
    rw [powerRadiusMap_directional]
    have he : (n:ℂ)*z^(n-1)*z = (n:ℂ)*z^n := by rw [mul_assoc,← pow_succ,Nat.sub_add_cancel hn]
    rw [he]
    simp [Complex.mul_re,Complex.normSq_apply]
  have hang : fderiv ℝ (powerRadiusMap n) z (Complex.I*z) =
      (-(n:ℝ)*(z^n).im,0) := by
    rw [powerRadiusMap_directional]
    have he : (n:ℂ)*z^(n-1)*(Complex.I*z) = Complex.I*((n:ℂ)*z^n) := by
      rw [show z^n = z^(n-1)*z by rw [← pow_succ,Nat.sub_add_cancel hn]]
      ring
    rw [he]
    simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.natCast_re,Complex.natCast_im,zero_mul,add_zero,zero_add,
      one_mul,sub_zero,zero_sub]
    congr 1 <;> ring
  rintro ⟨s,t⟩
  let β : ℝ := t/(2*Complex.normSq z)
  let α : ℝ := (β*(n:ℝ)*(z^n).re-s)/((n:ℝ)*(z^n).im)
  refine ⟨β • z + α • (Complex.I*z),?_⟩
  rw [map_add,map_smul,map_smul,hrad,hang]
  ext <;> dsimp [α,β] <;> field_simp [hn0,hz,hR] <;> ring

end

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
open Set Filter
open scoped Topology ContDiff ComplexConjugate
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

def roundPowerRadius (a b : Euclidean (d+1)) (k : ℕ) (p : Sphere d) : ℝ × ℝ :=
  powerRadiusMap k (planarLinear a b (p : Euclidean (d+1)))
lemma roundPowerRadius_chart (a b : Euclidean (d+1)) (k : ℕ) (p : Sphere d) :
    roundPowerRadius a b k ∘ (chartAt (Euclidean d) p).symm =
      powerRadiusMap k ∘ planarLinear a b ∘ roundChart (p : Euclidean (d+1)) (sphereFrame p) := by
  funext y
  change powerRadiusMap k (planarLinear a b ((chartAt (Euclidean d) p).symm y : Euclidean (d+1))) = _
  exact congrArg (fun z => powerRadiusMap k (planarLinear a b z)) (congrFun (sphere_chart_symm p) y)
lemma roundPowerRadius_chart_contDiff (a b : Euclidean (d+1)) (k : ℕ) (p : Sphere d) :
    ContDiff ℝ ∞ (roundPowerRadius a b k ∘ (chartAt (Euclidean d) p).symm) := by
  rw [roundPowerRadius_chart]
  exact (powerRadiusMap_contDiff k).comp ((planarLinear a b).contDiff.comp (roundChart_smooth _ _))

theorem roundPowerRadius_chart_surjective (a b : Euclidean (d+1)) (k : ℕ) (p : Sphere d)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (hk : 1 ≤ k) (hR : Complex.normSq (planarLinear a b (p : Euclidean (d+1))) < 1)
    (htheta : ((planarLinear a b (p : Euclidean (d+1)))^k).im ≠ 0) :
    Function.Surjective (fderiv ℝ (roundPowerRadius a b k ∘ (chartAt (Euclidean d) p).symm) 0) := by
  rw [roundPowerRadius_chart]
  rw [fderiv_comp 0 ((powerRadiusMap_contDiff k).differentiable (by simp) _)
    ((planarLinear a b).differentiableAt.comp 0 ((roundChart_smooth _ _).differentiable (by simp) _))]
  rw [fderiv_comp 0 (planarLinear a b).differentiableAt ((roundChart_smooth _ _).differentiable (by simp) _)]
  rw [ContinuousLinearMap.fderiv, (roundChart_first _ _).fderiv, Function.comp_apply,roundChart_zero]
  exact (powerRadiusMap_surjective k hk _ htheta).comp (planar_sphereFrame_surjective a b p ha hb hab hR)



end YauCounterexamples
end

end OAI
