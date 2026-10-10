import OAI.Analysis.PureInfiniteness.MultiplierIntertwining
import OAI.Analysis.JiangSu.Nonunital.ClosedIdealBasic

namespace OAI

/-! A closed ideal in a C*-ideal is an ideal in the containing algebra.
The proof uses the approximate unit of the smaller ideal. -/

noncomputable section
open Filter Topology

namespace WeakPureInfiniteness

universe u
variable {A B : Type u} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def idealImageHom (ι : A →⋆ₙₐ[ℂ] B) (J : NonunitalClosedIdeal.Ideal A) :
    NonunitalClosedIdeal.idealStarAlgebra J →⋆ₙₐ[ℂ] B :=
  ι.comp (NonunitalClosedIdeal.idealInclusion J)

theorem RightIdealRange.idealImage {ι : A →⋆ₙₐ[ℂ] B} (hι : RightIdealRange ι)
    (J : NonunitalClosedIdeal.Ideal A) : RightIdealRange (idealImageHom ι J) := by
  let f := idealImageHom ι J
  let E := NonunitalClosedIdeal.idealStarAlgebra J
  let hunit := CStarAlgebra.increasingApproximateUnit E
  intro x b
  obtain ⟨a, ha⟩ := ι.mem_range.mp (hι x.val b)
  have hlim : Tendsto (fun e : E => f (e * x) * b) (CStarAlgebra.approximateUnit E)
      (𝓝 (f x * b)) :=
    (((nonUnitalStarHom_continuous f).tendsto x).comp (hunit.tendsto_mul_right x)).mul_const b
  apply (nonUnitalStarHom_isClosed_range f).mem_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro e
  refine ⟨⟨e.val * a, J.mul_right e.val a e.property⟩, ?_⟩
  change ι (e.val * a) = ι (e.val * x.val) * b
  rw [map_mul, map_mul, ha, mul_assoc]

def idealInIdealImage (ι : A →⋆ₙₐ[ℂ] B) (hι : RightIdealRange ι)
    (J : NonunitalClosedIdeal.Ideal A) : NonunitalClosedIdeal.Ideal B where
  module := (idealImageHom ι J : NonunitalClosedIdeal.idealStarAlgebra J →ₗ[ℂ] B).range
  closed := nonUnitalStarHom_isClosed_range (idealImageHom ι J)
  mul_left a b hb := by
    obtain ⟨x, rfl⟩ := hb
    exact (hι.idealImage J).mul_left x a
  mul_right a b ha := by
    obtain ⟨x, rfl⟩ := ha
    exact hι.idealImage J x b
  star_mem a ha := by
    obtain ⟨x, rfl⟩ := ha
    exact ⟨star x, map_star (idealImageHom ι J) x⟩

@[simp] theorem mem_idealInIdealImage (ι : A →⋆ₙₐ[ℂ] B) (hι : RightIdealRange ι)
    (J : NonunitalClosedIdeal.Ideal A) (b : B) :
    b ∈ (idealInIdealImage ι hι J).module ↔ ∃ a ∈ J.module, ι a = b := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.val, a.property, ha⟩
  · rintro ⟨a, ha, hab⟩
    exact ⟨⟨a, ha⟩, hab⟩

end WeakPureInfiniteness

end

end OAI
