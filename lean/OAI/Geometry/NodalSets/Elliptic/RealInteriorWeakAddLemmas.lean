import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakRestrictionLemmas

namespace OAI

noncomputable section

namespace Yau

open MeasureTheory Set
open scoped ContDiff

theorem real_interior_weak_add {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (u v g h : Coord n → ℝ)
    (hu : MemLp u 2 (volume.restrict K)) (hv : MemLp v 2 (volume.restrict K))
    (hg : MemLp g 2 (volume.restrict K)) (hh : MemLp h 2 (volume.restrict K))
    (i : Fin n)
    (hw : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, u x*coordPartial psi x i)=-(∫ x in K, g x*psi x))
    (hvweak : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, v x*coordPartial psi x i)=-(∫ x in K, h x*psi x)) :
    MemLp (fun x ↦ u x+v x) 2 (volume.restrict K) ∧
    MemLp (fun x ↦ g x+h x) 2 (volume.restrict K) ∧
    ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      IntegrableOn (fun x ↦ (u x+v x)*coordPartial psi x i) K ∧
      IntegrableOn (fun x ↦ (g x+h x)*psi x) K ∧
      (∫ x in K, (u x+v x)*coordPartial psi x i)=-(∫ x in K, (g x+h x)*psi x) := by
  refine ⟨hu.add hv,hg.add hh,fun psi hp hc hs ↦ ?_⟩
  have ht := real_continuous_memLp_compact hK psi hp.continuous
  have hdt := real_continuous_memLp_compact hK _ (real_coordPartial_smooth psi hp i).continuous
  refine ⟨(hu.add hv).integrable_mul hdt,(hg.add hh).integrable_mul ht,?_⟩
  have hiu : IntegrableOn (fun x ↦ u x*coordPartial psi x i) K := hu.integrable_mul hdt
  have hiv : IntegrableOn (fun x ↦ v x*coordPartial psi x i) K := hv.integrable_mul hdt
  have hig : IntegrableOn (fun x ↦ g x*psi x) K := hg.integrable_mul ht
  have hih : IntegrableOn (fun x ↦ h x*psi x) K := hh.integrable_mul ht
  simp_rw [add_mul]
  rw [integral_add hiu hiv,
    integral_add hig hih,hw psi hp hc hs,hvweak psi hp hc hs]
  ring

def realWeakGradientCommutator {n : ℕ} (C : Coord n → Fin n → Fin n → ℝ)
    (U : Fin n → Coord n → ℝ) (k j : Fin n) (x : Coord n) : ℝ :=
  ∑ a, coordPartial (fun y ↦ C y a j) x k*U a x

def realWeakGradientCommutatorDerivative {n : ℕ} (C : Coord n → Fin n → Fin n → ℝ)
    (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ)
    (k j l : Fin n) (x : Coord n) : ℝ :=
  ∑ a, (coordPartial (fun y ↦ C y a j) x k*H a l x+
    coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y k) x l*U a x)

theorem real_weak_gradient_commutator_H1 {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (C : Coord n → Fin n → Fin n → ℝ) (U : Fin n → Coord n → ℝ)
    (H : Fin n → Fin n → Coord n → ℝ)
    (hC : ∀ a j, ContDiff ℝ ∞ (fun x ↦ C x a j))
    (hU : ∀ a, MemLp (U a) 2 (volume.restrict K))
    (hH : ∀ a l, MemLp (H a l) 2 (volume.restrict K))
    (hweak : ∀ a l psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, U a x*coordPartial psi x l)=-(∫ x in K, H a l x*psi x))
    (k j l : Fin n) :
    MemLp (realWeakGradientCommutator C U k j) 2 (volume.restrict K) ∧
    MemLp (realWeakGradientCommutatorDerivative C U H k j l) 2 (volume.restrict K) ∧
    ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      IntegrableOn (fun x ↦ realWeakGradientCommutator C U k j x*coordPartial psi x l) K ∧
      IntegrableOn (fun x ↦ realWeakGradientCommutatorDerivative C U H k j l x*psi x) K ∧
      (∫ x in K, realWeakGradientCommutator C U k j x*coordPartial psi x l) =
        -(∫ x in K, realWeakGradientCommutatorDerivative C U H k j l x*psi x) := by
  have hprod (a : Fin n) := real_interior_weak_product hK (U a) (H a l)
    (fun x ↦ coordPartial (fun y ↦ C y a j) x k) (hU a) (hH a l)
    (real_coordPartial_smooth _ (hC a j) k) l (hweak a l)
  exact real_interior_weak_sum hK _ _ (fun a ↦ (hprod a).1) (fun a ↦ (hprod a).2.1) l
    (fun a psi hp hc hs ↦ ((hprod a).2.2 psi hp hc hs).2.2)

end Yau

end

end OAI
