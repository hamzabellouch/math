import OAI.Geometry.NodalSets.Elliptic.RealWeakHessianSymmetry

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_weak_third_last_symmetry {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ)
    (J : Fin n → Fin n → Fin n → Coord n → ℝ)
    (hJ : ∀ a k i, MemLp (J a k i) 2 (volume.restrict K))
    (hH : ∀ a k psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, U a x*coordPartial psi x k)=-(∫ x in K, H a k x*psi x))
    (hthird : ∀ a k i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, H a k x*coordPartial psi x i)=-(∫ x in K, J a k i x*psi x))
    (a k i : Fin n) : J a k i =ᵐ[volume.restrict (interior K)] J a i k :=
  real_weak_hessian_symmetry hK (U a) (H a) (J a) (hJ a) (hH a) (hthird a) k i

theorem real_weak_third_first_symmetry {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (H : Fin n → Fin n → Coord n → ℝ) (J : Fin n → Fin n → Fin n → Coord n → ℝ)
    (hJ : ∀ a k i, MemLp (J a k i) 2 (volume.restrict K))
    (hsym : ∀ a k, H a k =ᵐ[volume.restrict K] H k a)
    (hthird : ∀ a k i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, H a k x*coordPartial psi x i)=-(∫ x in K, J a k i x*psi x))
    (a k i : Fin n) : J a k i =ᵐ[volume.restrict (interior K)] J k a i := by
  apply real_interior_L2_eq_of_test_pairings hK _ _ (hJ a k i) (hJ k a i)
  intro psi hp hc hs
  have h1 := hthird a k i psi hp hc hs
  have h2 := hthird k a i psi hp hc hs
  have hid : (∫ x in K, H a k x*coordPartial psi x i)=∫ x in K, H k a x*coordPartial psi x i := by
    apply integral_congr_ae
    filter_upwards [hsym a k] with x hx
    rw [hx]
  linarith only [h1,h2,hid]

end
end Yau

end OAI
