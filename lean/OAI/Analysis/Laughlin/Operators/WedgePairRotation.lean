import OAI.Analysis.Laughlin.Pair.CoupledBasis
import OAI.Analysis.Laughlin.Spin.Disjoint
import OAI.Analysis.Laughlin.Spin.Intertwining

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix Kronecker

theorem antisymmetric_ordered_sum (Q : ℕ) (f g : SpinIndex Q Q → ℂ)
    (hf : ∀ i j, f (j,i) = -f (i,j)) :
    (∑ i, f i*g i) = ∑ i : WedgePairIndex Q, f i.val * (g i.val-g i.val.swap) := by
  have hd (i : Fin (Q+1)) : f (i,i)=0 := by have := hf i i; linear_combination this / 2
  have he (i j : Fin (Q+1)) : f (i,j)*g (i,j) =
      (if i < j then f (i,j)*g (i,j) else 0) -
      (if j < i then f (j,i)*g (i,j) else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h,not_lt_of_gt h]
    · subst j; simp [hd]
    · simp [h,not_lt_of_gt h,hf i j]
  calc
    _ = ∑ i : Fin (Q+1), ∑ j : Fin (Q+1),
        ((if i < j then f (i,j)*g (i,j) else 0) -
        (if j < i then f (j,i)*g (i,j) else 0)) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      exact he i j
    _ = ∑ i : SpinIndex Q Q, if i.1 < i.2 then f i*(g i-g i.swap) else 0 := by
      simp only [Finset.sum_sub_distrib,Fintype.sum_prod_type]
      rw [Finset.sum_comm (f := fun i j : Fin (Q+1) => if j < i then f (j,i)*g (i,j) else 0)]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i hi
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j hj
      split_ifs <;> simp [mul_sub]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (p := fun i : SpinIndex Q Q => i.1 < i.2) (Finset.univ.filter (fun i : SpinIndex Q Q => i.1 < i.2))
        (by simp) (fun i => f i*(g i-g i.swap)))

noncomputable def wedgePairMatrix (Q : ℕ) (g : SourceSU2) :
    Matrix (WedgePairIndex Q) (WedgePairIndex Q) ℂ := fun i j =>
  sourceSpinRepresentation Q g i.val.1 j.val.1 * sourceSpinRepresentation Q g i.val.2 j.val.2 -
    sourceSpinRepresentation Q g i.val.1 j.val.2 * sourceSpinRepresentation Q g i.val.2 j.val.1

theorem wedgePairMatrix_tensor (Q : ℕ) (g : SourceSU2) (f : SpinIndex Q Q → ℂ)
    (hf : ∀ i j, f (j,i) = -f (i,j)) (i : WedgePairIndex Q) :
    (wedgePairMatrix Q g *ᵥ (fun j => (Real.sqrt 2 : ℂ)*f j.val)) i =
      (Real.sqrt 2 : ℂ) *
        ((sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g) *ᵥ f) i.val := by
  have h := antisymmetric_ordered_sum Q f
    (fun j => sourceSpinRepresentation Q g i.val.1 j.1 * sourceSpinRepresentation Q g i.val.2 j.2) hf
  simp only [Matrix.mulVec,dotProduct,Matrix.kroneckerMap,Matrix.of_apply]
  conv_rhs => rw [show (∑ j : SpinIndex Q Q,
    sourceSpinRepresentation Q g i.val.1 j.1 * sourceSpinRepresentation Q g i.val.2 j.2 * f j) =
    ∑ j : SpinIndex Q Q, f j*(sourceSpinRepresentation Q g i.val.1 j.1 *
      sourceSpinRepresentation Q g i.val.2 j.2) by apply Finset.sum_congr rfl; intro j hj; ring]
  rw [h,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [wedgePairMatrix]
  ring

theorem pairCoupledInclusion_SU2 (Q r : ℕ) (hr : r ≤ Q) (hor : Odd r) (g : SourceSU2) :
    wedgePairMatrix Q g * (pairCoupledInclusion Q r hr).map Complex.ofReal =
      (pairCoupledInclusion Q r hr).map Complex.ofReal *
        sourceSpinRepresentation (genericCoupledWeight Q Q r) g := by
  ext i n
  have hp : physicalCoupledInclusion Q Q r hr hr =
      (fun j k => (pairCoupledTensor Q r hr k.val j : ℂ)) := by
    ext j k
    simp [physicalCoupledInclusion,genericCoupledInclusion,pairCoupledTensor]
  have h := congrFun (congrFun (physicalCoupledInclusion_SU2 Q Q r hr hr g) i.val) n
  rw [hp] at h
  have hf (a b : Fin (Q+1)) :
      (pairCoupledTensor Q r hr n.val (b,a) : ℂ) = -(pairCoupledTensor Q r hr n.val (a,b) : ℂ) := by
    exact_mod_cast pairCoupledTensor_antisymmetric Q r n.val hr hor a b
  change (wedgePairMatrix Q g *ᵥ
    (fun j => (pairCoupledWedge Q r hr n.val j : ℂ))) i = _
  simp only [pairCoupledWedge,tensorToWedgePair,Complex.ofReal_mul]
  rw [wedgePairMatrix_tensor Q g (fun j : SpinIndex Q Q => (pairCoupledTensor Q r hr n.val j : ℂ)) hf i]
  change ((sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g) *ᵥ
    (fun j : SpinIndex Q Q => (pairCoupledTensor Q r hr n.val j : ℂ))) i.val =
      ∑ k, (pairCoupledTensor Q r hr k.val i.val : ℂ) *
        sourceSpinRepresentation (genericCoupledWeight Q Q r) g k n at h
  rw [h]
  simp only [Matrix.mul_apply,Matrix.map_apply,pairCoupledInclusion,pairCoupledWedge,
    tensorToWedgePair,Complex.ofReal_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end Laughlin.Spin

end OAI
