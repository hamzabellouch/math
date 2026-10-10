import OAI.Geometry.NodalSets.Elliptic.RealCompactTestDerivative
import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakUniqueness

namespace OAI

noncomputable section

namespace Yau

open MeasureTheory Set
open scoped ContDiff

theorem real_local_smooth_derivative_ae {n : ℕ} {Q : Set (Coord n)} (hQ : IsCompact Q)
    (u g v : Coord n → ℝ) (_ : MemLp u 2 (volume.restrict Q))
    (hg : MemLp g 2 (volume.restrict Q)) (hv : ContDiff ℝ ∞ v)
    (ha : v =ᵐ[volume.restrict Q] u) (i : Fin n)
    (hw : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, u x*coordPartial psi x i)=-(∫ x in Q, g x*psi x)) :
    (fun x ↦ coordPartial v x i) =ᵐ[volume.restrict (interior Q)] g := by
  apply real_interior_L2_eq_of_test_pairings hQ _ g
    (real_continuous_memLp_compact hQ _ (real_coordPartial_smooth v hv i).continuous) hg
  intro psi hp hc hs
  rw [(real_compact_test_derivative v psi hv hp hc i Q hs).2.2]
  have he : (∫ x in Q, v x*coordPartial psi x i)=(∫ x in Q, u x*coordPartial psi x i) :=
    integral_congr_ae (ha.mul Filter.EventuallyEq.rfl)
  rw [he,hw psi hp hc hs,neg_neg]

theorem real_smooth_divergence_equation {n : ℕ} {Q : Set (Coord n)} (hQ : IsCompact Q)
    (G : Fin n → Fin n → Coord n → ℝ) (hG : ∀ a j, ContDiff ℝ ∞ (G a j))
    (F : Coord n → ℝ) (hF : ContDiff ℝ ∞ F)
    (hw : ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∑ a, ∑ j, ∫ x in Q, G a j x*coordPartial psi x j)=∫ x in Q, F x*psi x) :
    ∀ x ∈ interior Q, -(∑ a, ∑ j, coordPartial (G a j) x j)=F x := by
  let D : Coord n → ℝ := fun x ↦ -(∑ a, ∑ j, coordPartial (G a j) x j)
  have hD : ContDiff ℝ ∞ D :=
    (ContDiff.sum (fun a _ ↦ ContDiff.sum (fun j _ ↦ real_coordPartial_smooth _ (hG a j) j))).neg
  have ha : D =ᵐ[volume.restrict (interior Q)] F := by
    apply real_interior_L2_eq_of_test_pairings hQ D F
      (real_continuous_memLp_compact hQ D hD.continuous)
      (real_continuous_memLp_compact hQ F hF.continuous)
    intro psi hp hc hs
    have hi (a j : Fin n) : IntegrableOn (fun x ↦ coordPartial (G a j) x j*psi x) Q :=
      (real_compact_test_derivative (G a j) psi (hG a j) hp hc j Q hs).1.integrableOn
    have hid : (fun x ↦ D x*psi x)=fun x ↦ -(∑ a, ∑ j, coordPartial (G a j) x j*psi x) := by
      funext x
      simp only [D,neg_mul,Finset.sum_mul]
    rw [hid,integral_neg,integral_finsetSum _ (fun a _ ↦ integrable_finsetSum _ (fun j _ ↦ hi a j))]
    simp_rw [integral_finsetSum _ (fun j _ ↦ hi _ j)]
    simp_rw [(real_compact_test_derivative _ psi (hG _ _) hp hc _ Q hs).2.2]
    simp only [Finset.sum_neg_distrib,neg_neg]
    exact hw psi hp hc hs
  exact Measure.eqOn_open_of_ae_eq ha isOpen_interior hD.continuous.continuousOn hF.continuous.continuousOn

end Yau

end

end OAI
