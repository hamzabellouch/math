import OAI.Analysis.Pureness.Divisibility.FullnessDensity
import Mathlib.RingTheory.SimpleRing.Field
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

namespace OAI
noncomputable section
namespace CuntzPureness
variable {A : Type*} [NormedRing A] [CompleteSpace A] [Nontrivial A]

theorem topologicallySimple_isSimpleRing (hsimple : TopologicallySimple A) :
    IsSimpleRing A := by
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  obtain ⟨a, ha, ha0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI)
  have ha0' : a ≠ 0 := by simpa using ha0
  obtain ⟨l, u, hu⟩ := exists_invertible_finiteIdealSum hsimple a ha0'
  have hsum : finiteIdealSum a l ∈ I := by
    clear hu
    induction l with
    | nil => exact I.zero_mem
    | cons p l ih =>
      exact I.add_mem (I.mul_mem_right _ _ (I.mul_mem_left _ _ ha)) ih
  have hunit : (u : A) ∈ I := hu.symm ▸ hsum
  apply TwoSidedIdeal.eq_top
  simpa using I.mul_mem_left (↑(u⁻¹)) (↑u) hunit

theorem simple_complex_center_scalar [NormedAlgebra ℂ A]
    (hsimple : TopologicallySimple A) (a : A)
    (hc : ∀ x : A, x*a=a*x) : ∃ c : ℂ, algebraMap ℂ A c = a := by
  let := topologicallySimple_isSimpleRing hsimple
  obtain ⟨c, hcsp⟩ := spectrum.nonempty a
  refine ⟨c, ?_⟩
  by_contra hne
  let z : Subring.center A := ⟨algebraMap ℂ A c - a,
    Subring.mem_center_iff.mpr (fun x => by
      rw [mul_sub,sub_mul,← Algebra.commutes c x,hc x])⟩
  have hz : z ≠ 0 := by
    intro h
    apply hne
    exact sub_eq_zero.mp (congrArg Subtype.val h)
  let := (IsSimpleRing.isField_center A).toField
  have hu : IsUnit (algebraMap ℂ A c - a) :=
    (isUnit_iff_ne_zero.mpr hz).map (Subring.center A).subtype
  exact (spectrum.mem_iff.mp hcsp) hu
end CuntzPureness

end

end OAI
