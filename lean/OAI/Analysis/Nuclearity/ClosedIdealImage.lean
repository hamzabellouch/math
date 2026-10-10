import OAI.Analysis.WeakInfiniteness.NonUnitalClosedRange
import OAI.Analysis.JiangSu.Nonunital.ClosedIdealBasic

namespace OAI

/-! The closed image ideal of a surjective star homomorphism. -/

noncomputable section
open scoped Topology

namespace WeakPureInfiniteness

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def closedIdealImage (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q)
    (J : NonunitalClosedIdeal.Ideal A) : NonunitalClosedIdeal.Ideal B where
  module := (J.module.map (q : A →ₗ[ℂ] B)).topologicalClosure
  closed := (J.module.map (q : A →ₗ[ℂ] B)).isClosed_topologicalClosure
  mul_left a b hb := by
    let M := J.module.map (q : A →ₗ[ℂ] B)
    let K := M.topologicalClosure
    obtain ⟨x, rfl⟩ := hq a
    apply closure_minimal (t := {b | q x * b ∈ K}) ?_
      (M.isClosed_topologicalClosure.preimage (continuous_const.mul continuous_id)) hb
    rintro _ ⟨y, hy, rfl⟩
    apply M.le_topologicalClosure
    exact ⟨x * y, J.mul_left x y hy, map_mul q x y⟩
  mul_right a b ha := by
    let M := J.module.map (q : A →ₗ[ℂ] B)
    let K := M.topologicalClosure
    obtain ⟨y, rfl⟩ := hq b
    apply closure_minimal (t := {a | a * q y ∈ K}) ?_
      (M.isClosed_topologicalClosure.preimage (continuous_id.mul continuous_const)) ha
    rintro _ ⟨x, hx, rfl⟩
    apply M.le_topologicalClosure
    exact ⟨x * y, J.mul_right x y hx, map_mul q x y⟩
  star_mem b hb := by
    let M := J.module.map (q : A →ₗ[ℂ] B)
    let K := M.topologicalClosure
    apply closure_minimal (t := {b | star b ∈ K}) ?_
      (M.isClosed_topologicalClosure.preimage continuous_star) hb
    rintro _ ⟨x, hx, rfl⟩
    apply M.le_topologicalClosure
    exact ⟨star x, J.star_mem x hx, map_star q x⟩

theorem mem_closedIdealImage (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q)
    (J : NonunitalClosedIdeal.Ideal A) (x : A) (hx : x ∈ J.module) :
    q x ∈ (closedIdealImage q hq J).module :=
  (J.module.map (q : A →ₗ[ℂ] B)).le_topologicalClosure ⟨x, hx, rfl⟩

theorem functional_zero_on_closedIdealImage (q : A →⋆ₙₐ[ℂ] B) (hq : Function.Surjective q)
    (J : NonunitalClosedIdeal.Ideal A) (F : B →L[ℂ] ℂ)
    (hF : ∀ x ∈ J.module, F (q x) = 0) :
    ∀ y ∈ (closedIdealImage q hq J).module, F y = 0 := by
  intro y hy
  apply closure_minimal (t := {y | F y = 0}) ?_ (isClosed_eq F.continuous continuous_const) hy
  rintro _ ⟨x, hx, rfl⟩
  exact hF x hx

end WeakPureInfiniteness

end

end OAI
