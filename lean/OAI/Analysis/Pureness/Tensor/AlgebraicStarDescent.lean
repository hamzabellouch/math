import OAI.Analysis.Pureness.Tensor.CommutingStarTensor

namespace OAI
noncomputable section
namespace CuntzPureness
variable {R S F : Type*} [Ring R] [StarAddMonoid R] [Algebra ℂ R]
variable [Ring S] [StarAddMonoid S] [Algebra ℂ S]
variable [Ring F] [StarAddMonoid F] [Algebra ℂ F]
variable (q : R →⋆ₐ[ℂ] S) (hq : Function.Surjective q) (g : R →⋆ₐ[ℂ] F)
variable (hg : ∀ z, q z = 0 → g z = 0)

include hg in
lemma algebraicStarDescent_representative (x : R) :
    g (Function.surjInv hq (q x)) = g x := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply hg
  rw [map_sub, Function.surjInv_eq hq, sub_self]

def algebraicStarDescent : S →⋆ₐ[ℂ] F := by
  let f : S → F := fun x => g (Function.surjInv hq x)
  have he (x : R) : f (q x) = g x := algebraicStarDescent_representative q hq g hg x
  exact {
    toFun := f
    map_zero' := by rw [← map_zero q, he, map_zero]
    map_one' := by rw [← map_one q, he, map_one]
    map_add' := by
      intro x y
      obtain ⟨a, rfl⟩ := hq x
      obtain ⟨b, rfl⟩ := hq y
      rw [← map_add, he, he, he, map_add]
    map_mul' := by
      intro x y
      obtain ⟨a, rfl⟩ := hq x
      obtain ⟨b, rfl⟩ := hq y
      rw [← map_mul, he, he, he, map_mul]
    commutes' := by
      intro c
      rw [← q.commutes]
      change f (q (algebraMap ℂ R c)) = _
      rw [he]
      exact g.commutes c
    map_star' := by
      intro x
      obtain ⟨a, rfl⟩ := hq x
      rw [← map_star, he, he, map_star] }

lemma algebraicStarDescent_apply (x : R) :
    algebraicStarDescent q hq g hg (q x) = g x :=
  algebraicStarDescent_representative q hq g hg x
end CuntzPureness

end

end OAI
