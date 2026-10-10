import Mathlib.Analysis.CStarAlgebra.Projection

namespace OAI
noncomputable section
namespace CuntzPureness
variable {D : Type*} [CStarAlgebra D]

theorem exists_central_annihilator_of_right_ideal
    (haw : ∀ S : Set D, ∃ e : D, IsStarProjection e ∧
      ∀ z, (∀ a ∈ S, a*z=0) ↔ e*z=z) (a : D) :
    ∃ e : D, IsStarProjection e ∧ (∀ x, Commute e x) ∧
      ∀ z, (∀ x, a*x*z=0) ↔ e*z=z := by
  obtain ⟨e,he,hann⟩ := haw (Set.range (fun x : D => a*x))
  have ha (z : D) : (∀ x, a*x*z=0) ↔ e*z=z := by
    simpa only [Set.forall_mem_range] using hann z
  have hae : ∀ x, a*x*e=0 := (ha e).mpr he.isIdempotentElem.eq
  have hinv (x : D) : e*(x*e)=x*e := (ha (x*e)).mp (by
    intro y
    simpa only [mul_assoc] using hae (y*x))
  have hother (x : D) : e*x*e=e*x := by
    have h := congrArg star (hinv (star x))
    simpa only [star_mul, star_star, he.isSelfAdjoint.star_eq, mul_assoc] using h
  refine ⟨e,he,?_,ha⟩
  intro x
  exact (hother x).symm.trans ((mul_assoc e x e).trans (hinv x))

theorem exists_nonzero_factor_corner
    (haw : ∀ S : Set D, ∃ e : D, IsStarProjection e ∧
      ∀ z, (∀ a ∈ S, a*z=0) ↔ e*z=z)
    (hcentral : ∀ e : D, IsStarProjection e → (∀ x, Commute e x) → e=0 ∨ e=1)
    (a b : D) (ha : a ≠ 0) (hb : b ≠ 0) : ∃ x : D, a*x*b ≠ 0 := by
  obtain ⟨e,he,hc,hann⟩ := exists_central_annihilator_of_right_ideal haw a
  have he0 : e=0 := by
    rcases hcentral e he hc with h0 | h1
    · exact h0
    · have heq := (hann e).mpr he.isIdempotentElem.eq 1
      simp only [h1, mul_one] at heq
      exact (ha heq).elim
  by_contra h
  push Not at h
  have heq := (hann b).mp h
  rw [he0, zero_mul] at heq
  exact hb heq.symm
end CuntzPureness

end

end OAI
