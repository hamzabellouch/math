import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakRestrictionLemmas

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_weak_equation_restrict {n : ℕ} {Q L : Set (Coord n)}
    (hL : MeasurableSet L) (hsub : Q ⊆ L)
    (C : Coord n → Fin n → Fin n → ℝ) (U : Fin n → Coord n → ℝ) (F : Coord n → ℝ)
    (heq : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ L →
      (∑ a, ∑ j, ∫ x in L, C x a j*U a x*coordPartial psi x j)=∫ x in L, F x*psi x)
    (psi : Coord n → ℝ) (hp : ContDiff ℝ ∞ psi)
    (hc : HasCompactSupport psi) (hs : tsupport psi ⊆ Q) :
    (∑ a, ∑ j, ∫ x in Q, C x a j*U a x*coordPartial psi x j)=∫ x in Q, F x*psi x := by
  have h := heq psi hp hc (hs.trans hsub)
  have hflux (a j : Fin n) : (∫ x in L, C x a j*U a x*coordPartial psi x j)=
      ∫ x in Q, C x a j*U a x*coordPartial psi x j := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hL hsub
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := fun y ↦ coordPartial psi y j)
      (fun ht ↦ hx.2 (hs (tsupport_fderiv_apply_subset ℝ (Pi.single j 1) ht))),mul_zero]
  have hscalar : (∫ x in L, F x*psi x)=∫ x in Q, F x*psi x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hL hsub
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx.2 (hs ht)),mul_zero]
  simpa only [hflux,hscalar] using h

end
end Yau

end OAI
