import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakAddLemmas

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

def realSecondCommutator {n : ℕ} (C : Coord n → Fin n → Fin n → ℝ)
    (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ)
    (k l j : Fin n) (x : Coord n) : ℝ :=
  ∑ a, (coordPartial (fun y ↦ C y a j) x l*H a k x+
    coordPartial (fun y ↦ C y a j) x k*H a l x+
    coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y k) x l*U a x)

def realSecondCommutatorDerivative {n : ℕ} (C : Coord n → Fin n → Fin n → ℝ)
    (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ)
    (J : Fin n → Fin n → Fin n → Coord n → ℝ) (k l j i : Fin n) (x : Coord n) : ℝ :=
  ∑ a, ((coordPartial (fun y ↦ C y a j) x l*J a k i x+
    coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y l) x i*H a k x)+
    (coordPartial (fun y ↦ C y a j) x k*J a l i x+
    coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y k) x i*H a l x)+
    (coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y k) x l*H a i x+
    coordPartial (fun y ↦ coordPartial (fun z ↦ coordPartial (fun t ↦ C t a j) z k) y l) x i*U a x))

theorem real_second_commutator_split {n : ℕ} (C : Coord n → Fin n → Fin n → ℝ)
    (U : Fin n → Coord n → ℝ) (H : Fin n → Fin n → Coord n → ℝ)
    (k l j : Fin n) (x : Coord n) :
    realWeakGradientCommutator C (fun a ↦ H a k) l j x+
      realWeakGradientCommutatorDerivative C U H k j l x=realSecondCommutator C U H k l j x := by
  simp only [realWeakGradientCommutator,realWeakGradientCommutatorDerivative,
    realSecondCommutator,Finset.sum_add_distrib,add_assoc]

theorem real_weak_second_commutator_H1 {n : ℕ} {K : Set (Coord n)} (hK : IsCompact K)
    (C : Coord n → Fin n → Fin n → ℝ) (U : Fin n → Coord n → ℝ)
    (H : Fin n → Fin n → Coord n → ℝ) (J : Fin n → Fin n → Fin n → Coord n → ℝ)
    (hC : ∀ a j, ContDiff ℝ ∞ (fun x ↦ C x a j))
    (hU : ∀ a, MemLp (U a) 2 (volume.restrict K))
    (hH : ∀ a k, MemLp (H a k) 2 (volume.restrict K))
    (hJ : ∀ a k i, MemLp (J a k i) 2 (volume.restrict K))
    (hsecond : ∀ a k psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, U a x*coordPartial psi x k)=-(∫ x in K, H a k x*psi x))
    (hthird : ∀ a k i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      (∫ x in K, H a k x*coordPartial psi x i)=-(∫ x in K, J a k i x*psi x))
    (k l j i : Fin n) :
    MemLp (realSecondCommutator C U H k l j) 2 (volume.restrict K) ∧
    MemLp (realSecondCommutatorDerivative C U H J k l j i) 2 (volume.restrict K) ∧
    ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ K →
      IntegrableOn (fun x ↦ realSecondCommutator C U H k l j x*coordPartial psi x i) K ∧
      IntegrableOn (fun x ↦ realSecondCommutatorDerivative C U H J k l j i x*psi x) K ∧
      (∫ x in K, realSecondCommutator C U H k l j x*coordPartial psi x i) =
        -(∫ x in K, realSecondCommutatorDerivative C U H J k l j i x*psi x) := by
  have h1 (a : Fin n) := real_interior_weak_product hK (H a k) (J a k i)
    (fun x ↦ coordPartial (fun y ↦ C y a j) x l) (hH a k) (hJ a k i)
    (real_coordPartial_smooth _ (hC a j) l) i (hthird a k i)
  have h2 (a : Fin n) := real_interior_weak_product hK (H a l) (J a l i)
    (fun x ↦ coordPartial (fun y ↦ C y a j) x k) (hH a l) (hJ a l i)
    (real_coordPartial_smooth _ (hC a j) k) i (hthird a l i)
  have h3 (a : Fin n) := real_interior_weak_product hK (U a) (H a i)
    (fun x ↦ coordPartial (fun y ↦ coordPartial (fun z ↦ C z a j) y k) x l)
    (hU a) (hH a i) (real_coordPartial_smooth _ (real_coordPartial_smooth _ (hC a j) k) l)
    i (hsecond a i)
  have h12 (a : Fin n) := real_interior_weak_add hK _ _ _ _
    (h1 a).1 (h2 a).1 (h1 a).2.1 (h2 a).2.1 i
    (fun psi hp hc hs ↦ ((h1 a).2.2 psi hp hc hs).2.2)
    (fun psi hp hc hs ↦ ((h2 a).2.2 psi hp hc hs).2.2)
  have h123 (a : Fin n) := real_interior_weak_add hK _ _ _ _
    (h12 a).1 (h3 a).1 (h12 a).2.1 (h3 a).2.1 i
    (fun psi hp hc hs ↦ ((h12 a).2.2 psi hp hc hs).2.2)
    (fun psi hp hc hs ↦ ((h3 a).2.2 psi hp hc hs).2.2)
  exact real_interior_weak_sum hK _ _ (fun a ↦ (h123 a).1) (fun a ↦ (h123 a).2.1) i
    (fun a psi hp hc hs ↦ ((h123 a).2.2 psi hp hc hs).2.2)

end
end Yau

end OAI
