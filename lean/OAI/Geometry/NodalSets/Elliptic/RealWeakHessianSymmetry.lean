import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakUniqueness

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_weak_hessian_symmetry {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (w : Coord n → ℝ) (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ)
    (hH : ∀ a i, MemLp (H a i) 2 (volume.restrict K))
    (hfirst : ∀ a psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, w x*coordPartial psi x a)=-(∫ x in K, U a x*psi x))
    (hsecond : ∀ a i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, U a x*coordPartial psi x i)=-(∫ x in K, H a i x*psi x))
    (a i : Fin n) : H a i =ᵐ[volume.restrict (interior K)] H i a := by
  apply real_interior_L2_eq_of_test_pairings hK _ _ (hH a i) (hH i a)
  intro psi hp hc hs
  have hd (j : Fin n) := real_coordPartial_smooth psi hp j
  have hdc (j : Fin n) := hc.fderiv_apply ℝ (Pi.single j 1)
  have hds (j : Fin n) := (tsupport_fderiv_apply_subset ℝ (Pi.single j 1) (f := psi)).trans hs
  have h1 := hsecond a i psi hp hc hs
  have h2 := hsecond i a psi hp hc hs
  have h3 := hfirst a (fun x ↦ coordPartial psi x i) (hd i) (hdc i) (hds i)
  have h4 := hfirst i (fun x ↦ coordPartial psi x a) (hd a) (hdc a) (hds a)
  have hcomm : (fun x ↦ w x*coordPartial (fun y ↦ coordPartial psi y i) x a) =
      fun x ↦ w x*coordPartial (fun y ↦ coordPartial psi y a) x i := by
    funext x
    rw [real_coordPartial_commute psi hp x a i]
  rw [hcomm] at h3
  linarith only [h1,h2,h3,h4]

end
end Yau

end OAI
