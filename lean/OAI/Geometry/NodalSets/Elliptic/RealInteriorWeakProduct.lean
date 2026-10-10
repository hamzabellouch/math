import OAI.Geometry.NodalSets.Elliptic.RealCompactMultiplierLemmas
import OAI.Geometry.NodalSets.Elliptic.RealDifferenceQuotientTest

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_interior_weak_product {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (u g a : Coord n → ℝ) (hu : MemLp u 2 (volume.restrict K))
    (hg : MemLp g 2 (volume.restrict K)) (ha : ContDiff ℝ ∞ a) (i : Fin n)
    (hweak : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, u x*coordPartial psi x i)=-(∫ x in K, g x*psi x)) :
    MemLp (fun x ↦ a x*u x) 2 (volume.restrict K) ∧
    MemLp (fun x ↦ a x*g x+coordPartial a x i*u x) 2 (volume.restrict K) ∧
    ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      IntegrableOn (fun x ↦ (a x*u x)*coordPartial psi x i) K ∧
      IntegrableOn (fun x ↦ (a x*g x+coordPartial a x i*u x)*psi x) K ∧
      (∫ x in K, (a x*u x)*coordPartial psi x i) =
        -(∫ x in K, (a x*g x+coordPartial a x i*u x)*psi x) := by
  obtain ⟨_,_,hba⟩ := real_compact_multiplier_bound hK a ha.continuous
  obtain ⟨_,_,hbd⟩ := real_compact_multiplier_bound hK (fun x ↦ coordPartial a x i)
    (real_coordPartial_smooth a ha i).continuous
  have hau := (hba u hu).1
  have hag := (hba g hg).1
  have hdu := (hbd u hu).1
  refine ⟨hau,hag.add hdu,fun psi hp hc hs ↦ ?_⟩
  have hpsi := real_continuous_memLp_compact hK psi hp.continuous
  have hdpsi := real_continuous_memLp_compact hK _ (real_coordPartial_smooth psi hp i).continuous
  have hi1 : IntegrableOn (fun x ↦ (a x*u x)*coordPartial psi x i) K := hau.integrable_mul hdpsi
  have hi2 : IntegrableOn (fun x ↦ (a x*g x)*psi x) K := hag.integrable_mul hpsi
  have hi3 : IntegrableOn (fun x ↦ (coordPartial a x i*u x)*psi x) K := hdu.integrable_mul hpsi
  have heq := hweak (fun x ↦ a x*psi x) (ha.mul hp) hc.mul_left (tsupport_mul_subset_right.trans hs)
  have heleft : (fun x ↦ u x*coordPartial (fun y ↦ a y*psi y) x i) =
      fun x ↦ (coordPartial a x i*u x)*psi x+(a x*u x)*coordPartial psi x i := by
    funext x
    rw [real_coordPartial_mul a psi ha hp]
    ring
  have heright : (fun x ↦ g x*(a x*psi x)) = fun x ↦ (a x*g x)*psi x := by funext x; ring
  rw [heleft,heright,integral_add hi3 hi1] at heq
  have heprod : (fun x ↦ (a x*g x+coordPartial a x i*u x)*psi x) =
      fun x ↦ (a x*g x)*psi x+(coordPartial a x i*u x)*psi x := by funext x; ring
  refine ⟨hi1,(hag.add hdu).integrable_mul hpsi,?_⟩
  rw [heprod,integral_add hi2 hi3]
  linarith only [heq]

end
end Yau

end OAI
