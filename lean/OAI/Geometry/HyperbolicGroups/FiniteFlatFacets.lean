import Mathlib

namespace OAI

section


noncomputable section
namespace HyperbolicObstruction
variable {V G : Type*} [DecidableEq V] [Group G]
variable (f : V → V → G) (hs : ∀ a, f a a = 1)
  (hr : ∀ a b, f b a = (f a b)⁻¹)

include hs hr

lemma flat_three_potential {a b c : V} (h : f a b * f b c = f a c)
    {x y : V} (hx : x ∈ ({a,b,c} : Finset V)) (hy : y ∈ ({a,b,c} : Finset V)) :
    f x y = (f a x)⁻¹ * f a y := by
  have hbc : f b c = (f a b)⁻¹ * f a c := by rw [← h]; simp
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with hx|hx|hx <;> rcases hy with hy|hy|hy <;> subst x <;> subst y
  · simp [hs]
  · simp [hs]
  · simp [hs]
  · simp [hs,hr a b]
  · simp [hs]
  · exact hbc
  · simp [hs,hr a c]
  · rw [hr b c,hbc,mul_inv_rev,inv_inv]
  · simp [hs]

lemma flat_three {a b c : V} (h : f a b * f b c = f a c)
    {x y z : V} (hx : x ∈ ({a,b,c} : Finset V)) (hy : y ∈ ({a,b,c} : Finset V))
    (hz : z ∈ ({a,b,c} : Finset V)) : f x y * f y z = f x z := by
  rw [flat_three_potential f hs hr h hx hy,flat_three_potential f hs hr h hy hz,
    flat_three_potential f hs hr h hx hz]
  simp [mul_assoc]

lemma flat_two {a b x y z : V} (hx : x ∈ ({a,b} : Finset V))
    (hy : y ∈ ({a,b} : Finset V)) (hz : z ∈ ({a,b} : Finset V)) :
    f x y * f y z = f x z := by
  exact flat_three f hs hr (a := a) (b := b) (c := b) (by simp [hs])
    (by simpa using hx) (by simpa using hy) (by simpa using hz)
end HyperbolicObstruction
end
end

section

end

end OAI
