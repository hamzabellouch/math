import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.SphereProjection

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
section Plane
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem planar_tangent_surjective (a b p : E)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (hp : inner ℝ p p = 1) (hR : Complex.normSq (planarLinear a b p) < 1) :
    ∀ z : ℂ, ∃ v : E, inner ℝ p v = 0 ∧ planarLinear a b v = z := by
  intro z
  have hba : inner ℝ b a = 0 := (real_inner_comm a b).trans hab
  let A := inner ℝ a p
  let B := inner ℝ b p
  let R := A*A+B*B
  have hR' : R < 1 := by
    simpa [R,A,B,planarLinear_apply,Complex.normSq_apply] using hR
  have hden : 1-R ≠ 0 := (sub_pos.mpr hR').ne'
  let q := p - (A • a + B • b)
  let w := z.re • a + z.im • b
  have hqa : inner ℝ a q = 0 := by simp only [q,A,B,inner_sub_right,inner_add_right,inner_smul_right,ha,hab,mul_one,mul_zero,add_zero,sub_self]
  have hqb : inner ℝ b q = 0 := by simp only [q,A,B,inner_sub_right,inner_add_right,inner_smul_right,hb,hba,mul_one,mul_zero,zero_add,sub_self]
  have hqp : inner ℝ p q = 1-R := by
    simp only [q,inner_sub_right,inner_add_right,inner_smul_right,hp]
    rw [real_inner_comm a p,real_inner_comm b p]
  have hqz : planarLinear a b q = 0 := by simp [planarLinear_apply,hqa,hqb]
  have hw : planarLinear a b w = z := by
    simp only [planarLinear_apply,w,inner_add_right,inner_smul_right,ha,hb,hab,hba,
      mul_one,mul_zero,add_zero,zero_add]
    simpa only [mul_comm Complex.I] using Complex.re_add_im z
  refine ⟨w - (inner ℝ p w / (1-R)) • q, ?_, ?_⟩
  · rw [inner_sub_right,inner_smul_right,hqp,div_mul_cancel₀ _ hden,sub_self]
  · rw [map_sub,map_smul,hqz,smul_zero,sub_zero,hw]
end Plane
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩
lemma planar_sphereFrame_surjective (a b : Euclidean (d+1)) (p : Sphere d)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (hR : Complex.normSq (planarLinear a b (p : Euclidean (d+1))) < 1) :
    Function.Surjective ((planarLinear a b).comp (sphereFrame p).toContinuousLinearMap) := by
  intro z
  have hp : inner ℝ (p : Euclidean (d+1)) (p : Euclidean (d+1)) = 1 := by
    rw [real_inner_self_eq_norm_sq]
    simp
  obtain ⟨v,hpv,hv⟩ := planar_tangent_surjective a b (p : Euclidean (d+1)) ha hb hab hp hR z
  refine ⟨sphereCoordinates p v,?_⟩
  change planarLinear a b (sphereFrame p (sphereCoordinates p v)) = z
  rw [sphereFrame_coordinates]
  simpa only [sphereProjection,hpv,zero_smul,sub_zero] using hv
end YauCounterexamples

end

end OAI
