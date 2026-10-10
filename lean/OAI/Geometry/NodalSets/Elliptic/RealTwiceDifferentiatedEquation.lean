import OAI.Geometry.NodalSets.Elliptic.RealWeakDivergenceDifferentiation
import OAI.Geometry.NodalSets.Elliptic.RealWeakSecondCommutator
import OAI.Geometry.NodalSets.Elliptic.RealWeakSecondForcing

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_twice_differentiated_equation {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (C : Coord n → Fin n → Fin n → ℝ) (B w : Coord n → ℝ)
    (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ)
    (J : Fin n → Fin n → Fin n → Coord n → ℝ)
    (hC : ∀ a j, ContDiff ℝ ∞ (fun x ↦ C x a j)) (hB : ContDiff ℝ ∞ B)
    (hw : MemLp w 2 (volume.restrict K))
    (hU : ∀ a, MemLp (U a) 2 (volume.restrict K))
    (hH : ∀ a k, MemLp (H a k) 2 (volume.restrict K))
    (hJ : ∀ a k l, MemLp (J a k l) 2 (volume.restrict K))
    (hfirst : ∀ a psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, w x*coordPartial psi x a)=-(∫ x in K, U a x*psi x))
    (hsecond : ∀ a k psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, U a x*coordPartial psi x k)=-(∫ x in K, H a k x*psi x))
    (hthird : ∀ a k l psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, H a k x*coordPartial psi x l)=-(∫ x in K, J a k l x*psi x))
    (heq : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∑ a, ∑ j, ∫ x in K, C x a j*U a x*coordPartial psi x j) = ∫ x in K, B x*w x*psi x)
    (k l : Fin n) (psi : Coord n → ℝ) (hp : ContDiff ℝ ∞ psi)
    (hc : HasCompactSupport psi) (hs : tsupport psi ⊆ K) :
    (∀ a j, IntegrableOn (fun x ↦ C x a j*J a k l x*coordPartial psi x j) K) ∧
    IntegrableOn (fun x ↦ realSecondScalarForcing B w U H k l x*psi x) K ∧
    (∀ j, IntegrableOn (fun x ↦ realSecondCommutator C U H k l j x*coordPartial psi x j) K) ∧
    (∑ a, ∑ j, ∫ x in K, C x a j*J a k l x*coordPartial psi x j) =
      (∫ x in K, realSecondScalarForcing B w U H k l x*psi x)-
        ∑ j, ∫ x in K, realSecondCommutator C U H k l j x*coordPartial psi x j := by
  have hBF := real_interior_weak_product hK w (U k) B hw (hU k) hB k (hfirst k)
  have heq1 : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∑ a, ∑ j, ∫ x in K, C x a j*H a k x*coordPartial psi x j) =
        (∫ x in K, (B x*U k x+coordPartial B x k*w x)*psi x)-
          ∑ j, ∫ x in K, realWeakGradientCommutator C U k j x*coordPartial psi x j := by
    intro phi hphi hcp hsp
    have h := (real_weak_equation_differentiation hK C U H (fun x ↦ B x*w x)
      hC hU hH hBF.1 hsecond heq k phi hphi hcp hsp).2.2
    rw [(hBF.2.2 phi hphi hcp hsp).2.2,neg_neg] at h
    have hci (a j : Fin n) : IntegrableOn
        (fun x ↦ coordPartial (fun y ↦ C y a j) x k*U a x*coordPartial phi x j) K := by
      obtain ⟨_,_,hb⟩ := real_compact_multiplier_bound hK _
        (real_coordPartial_smooth _ (hC a j) k).continuous
      exact (hb _ (hU a)).1.integrable_mul
        (real_continuous_memLp_compact hK _ (real_coordPartial_smooth phi hphi j).continuous)
    simp only [realWeakGradientCommutator,Finset.sum_mul]
    simp_rw [integral_finsetSum Finset.univ (fun a _ ↦ hci a _)]
    rw [Finset.sum_comm (f := fun j a ↦ ∫ x in K,
      coordPartial (fun y ↦ C y a j) x k*U a x*coordPartial phi x j)]
    exact h
  have hscalar := real_weak_second_scalar_forcing hK B w U H hB hw hU hH hfirst hsecond k l
  have hcomm (j : Fin n) := real_weak_gradient_commutator_H1 hK C U H hC hU hH hsecond k j l
  have h := real_weak_divergence_equation_differentiation hK C (fun a ↦ H a k)
    (fun a ↦ J a k l) (realWeakGradientCommutator C U k)
    (fun j ↦ realWeakGradientCommutatorDerivative C U H k j l)
    (fun x ↦ B x*U k x+coordPartial B x k*w x) (realSecondScalarForcing B w U H k l)
    hC (fun a ↦ hH a k) (fun a ↦ hJ a k l) (fun j ↦ (hcomm j).1)
    (fun j ↦ (hcomm j).2.1) hscalar.1 hscalar.2.1 l (fun a ↦ hthird a k l)
    (fun j phi hphi hcp hsp ↦ ((hcomm j).2.2 phi hphi hcp hsp).2.2)
    (fun phi hphi hcp hsp ↦ (hscalar.2.2 phi hphi hcp hsp).2.2)
    heq1 psi hp hc hs
  simpa only [real_second_commutator_split] using h

end
end Yau

end OAI
