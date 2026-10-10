import Mathlib

namespace OAI

section
namespace ElementaryPositivity.PlanarRayOrder
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
include hB

lemma alternating_swap (x y : E) : B y x= -B x y := by
  have H:=hB (x+y)
  simp only [map_add,LinearMap.add_apply,hB,zero_add,add_zero] at H
  linarith

lemma plane_determinant (L : Module.Dual ℝ E) (r s m n : E)
    (hm : m∈Submodule.span ℝ {r,s}) (hn : n∈Submodule.span ℝ {r,s}) :
    L r*B m n=B m r*L n-L m*B n r := by
  obtain ⟨a,b,rfl⟩:=Submodule.mem_span_pair.mp hm
  obtain ⟨c,d,rfl⟩:=Submodule.mem_span_pair.mp hn
  simp only [map_add,LinearMap.add_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,hB,
    mul_zero,zero_add,add_zero,alternating_swap B hB s r]
  ring

lemma plane_normalized_eq (L : Module.Dual ℝ E) (r s m p : E) (hrs : B r s≠0)
    (hm : m∈Submodule.span ℝ {r,s}) (hp : p∈Submodule.span ℝ {r,s}) (hmp : B m p=0) :
    L p • m=L m • p := by
  obtain ⟨a,b,rfl⟩:=Submodule.mem_span_pair.mp hm
  obtain ⟨c,d,rfl⟩:=Submodule.mem_span_pair.mp hp
  have he : a*d=b*c:=by
    have hh : (a*d-b*c)*B r s=0:=by
      simp only [map_add,LinearMap.add_apply,map_smul,LinearMap.smul_apply,smul_eq_mul,hB,
        mul_zero,zero_add,add_zero,alternating_swap B hB r s] at hmp
      nlinarith only [hmp]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hrs)
  simp only [map_add,map_smul,smul_eq_mul,smul_add,smul_smul]
  congr 1
  · congr 1
    calc
      (c*L r+d*L s)*a=(a*c)*L r+(a*d)*L s:=by ring
      _=(a*L r+b*L s)*c:=by rw [he]; ring
  · congr 1
    calc
      (c*L r+d*L s)*b=(b*c)*L r+(b*d)*L s:=by ring
      _=(a*L r+b*L s)*d:=by rw [←he]; ring

def slope (L : Module.Dual ℝ E) (r m : E) : ℝ := B m r/L m

lemma pairing_pos_iff (L : Module.Dual ℝ E) (r s m n : E)
    (hr : 0<L r) (hm : 0<L m) (hn : 0<L n)
    (hmP : m∈Submodule.span ℝ {r,s}) (hnP : n∈Submodule.span ℝ {r,s}) :
    0<B m n ↔ slope B L r n<slope B L r m := by
  rw [slope,slope,div_lt_div_iff₀ hn hm]
  have he:=plane_determinant B hB L r s m n hmP hnP
  constructor <;> intro hh <;> nlinarith

lemma pairing_zero_iff (L : Module.Dual ℝ E) (r s m n : E)
    (hr : 0<L r) (hm : 0<L m) (hn : 0<L n)
    (hmP : m∈Submodule.span ℝ {r,s}) (hnP : n∈Submodule.span ℝ {r,s}) :
    B m n=0 ↔ slope B L r n=slope B L r m := by
  rw [slope,slope,div_eq_div_iff (ne_of_gt hn) (ne_of_gt hm)]
  have he:=plane_determinant B hB L r s m n hmP hnP
  constructor <;> intro hh <;> nlinarith
end
end ElementaryPositivity.PlanarRayOrder

end

end OAI
