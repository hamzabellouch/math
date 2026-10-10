import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorFunctor
import Mathlib.LinearAlgebra.Pi

namespace OAI

noncomputable section

namespace ArExplicit.BalancedTensor

variable {k R S F M : Type*} [CommRing k] [Ring R] [Algebra k R] [Ring S]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F]
variable [Module S F] [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Algebra k R] [IsScalarTower k R M] [Fintype ι] [DecidableEq ι] in
theorem tmul_sum (f : F) (s : Finset ι) (m : ι → M) :
    tmul (k := k) (R := R) f (∑ i ∈ s, m i) = ∑ i ∈ s, tmul f (m i) := by
  exact map_sum (mk (k := k) (R := R) f) m s

def piRightMap : BalancedTensor k R F (ι → M) →ₗ[S] (ι → BalancedTensor k R F M) :=
  LinearMap.pi fun i => mapRight (k := k) (S := S) (LinearMap.proj i)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem piRightMap_tmul (f : F) (m : ι → M) (i : ι) :
    piRightMap (S := S) (tmul f m : BalancedTensor k R F (ι → M)) i = tmul f (m i) := rfl

def piRightInv : (ι → BalancedTensor k R F M) →ₗ[S] BalancedTensor k R F (ι → M) where
  toFun z := ∑ i, mapRight (k := k) (S := S) (LinearMap.single R (fun _ : ι => M) i) (z i)
  map_add' x y := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' s z := by simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

omit [Fintype ι] in
theorem piRightMap_single (i j : ι) (z : BalancedTensor k R F M) :
    piRightMap (S := S) (mapRight (k := k) (S := S) (LinearMap.single R (fun _ : ι => M) j) z) i = if i = j then z else 0 := by
  induction z using induction_on with
  | zero => simp
  | tmul f m =>
    simp only [mapRight_tmul, piRightMap_tmul, LinearMap.single_apply]
    by_cases h : i = j
    · subst i; simp
    · simp [h]
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]
    split_ifs <;> simp

def piRight : BalancedTensor k R F (ι → M) ≃ₗ[S] (ι → BalancedTensor k R F M) where
  __ := piRightMap
  invFun := piRightInv
  right_inv z := by
    ext i
    change piRightMap (S := S) (∑ j, mapRight (k := k) (S := S) (LinearMap.single R (fun _ : ι => M) j) (z j)) i = z i
    simp only [map_sum, Finset.sum_apply, piRightMap_single]
    simp
  left_inv z := by
    change piRightInv (S := S) (piRightMap (S := S) z) = z
    induction z using induction_on with
    | zero => simp
    | tmul f m =>
      change (∑ i, tmul (k := k) (R := R) f (Pi.single i (m i))) = tmul f m
      rw [← tmul_sum]
      congr
      exact Finset.univ_sum_single m
    | add x y hx hy => simp only [map_add, hx, hy]

end ArExplicit.BalancedTensor

end

end OAI
