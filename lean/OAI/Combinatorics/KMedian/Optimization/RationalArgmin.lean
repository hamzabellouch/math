import Mathlib

namespace OAI

section
section
namespace MetricKMedian
open Finset

def rationalArgmin (A : Finset ℚ) (f : ℚ → ℚ) : ℚ :=
  if hA : A.Nonempty then
    let v := (A.image f).min' (hA.image f)
    let B := A.filter (fun t => f t=v)
    if hB : B.Nonempty then B.min' hB else 0
  else 0

theorem rationalArgmin_spec (A : Finset ℚ) (f : ℚ → ℚ) (hA : A.Nonempty) :
    rationalArgmin A f ∈ A ∧ ∀ t ∈ A, f (rationalArgmin A f) ≤ f t := by
  let v := (A.image f).min' (hA.image f)
  let B := A.filter (fun t => f t=v)
  have hB : B.Nonempty := by
    obtain ⟨t,ht,he⟩ := mem_image.mp (min'_mem (A.image f) (hA.image f))
    exact ⟨t,mem_filter.mpr ⟨ht,he⟩⟩
  have heq : rationalArgmin A f=B.min' hB := by
    simp only [rationalArgmin,dite_eq_left hA]
    change (if h : B.Nonempty then B.min' h else 0)=_
    rw [dite_eq_left hB]
  rw [heq]
  obtain ⟨h1,h2⟩ := mem_filter.mp (min'_mem B hB)
  refine ⟨h1,?_⟩
  intro t ht
  rw [h2]
  exact min'_le (A.image f) _ (mem_image_of_mem f ht)

end MetricKMedian
end
end

end OAI
