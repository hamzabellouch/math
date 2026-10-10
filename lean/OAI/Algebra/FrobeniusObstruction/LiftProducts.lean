import Mathlib
import OAI.Algebra.FrobeniusObstruction.SelectedCycles

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.ThreeParameters
variable {k : Type*} [Field k] {d : ℕ}

                                                             
def chosen (i j l : Fin d) (r : Fin d) : Ring k :=
  if r = i then s k 0 else if r = j then s k 1 else if r = l then s k 2 else 0

 theorem chosen_augmentation (i j l r : Fin d) :
    augmentation k (chosen (k := k) i j l r) = 0 := by
  simp only [chosen]
  split_ifs <;> simp only [augmentation_s, map_zero]

 theorem chosen_square (i j l r : Fin d) :
    chosen (k := k) i j l r * chosen (k := k) i j l r = 0 := by
  simp only [chosen]
  split_ifs <;> simp only [← pow_two, s_sq, zero_pow (by decide : 2 ≠ 0)]

 theorem chosen_outside (J : Finset (Fin d)) (i j l : Fin d)
    (hi : i ∈ J) (hj : j ∈ J) (hl : l ∈ J) (r : Fin d) (hr : r ∉ J) :
    chosen (k := k) i j l r = 0 := by
  have hri : r ≠ i := by rintro rfl; exact hr hi
  have hrj : r ≠ j := by rintro rfl; exact hr hj
  have hrl : r ≠ l := by rintro rfl; exact hr hl
  simp only [chosen, ite_eq_right hri, ite_eq_right hrj, ite_eq_right hrl]

 theorem chosen_product (i j l : Fin d) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    chosen (k := k) i j l i * chosen (k := k) i j l j * chosen (k := k) i j l l = w k := by
  simp [chosen, hij.symm, hil.symm, hjl.symm, w]

end BoundaryOnly.FormalObstruction.ThreeParameters

namespace BoundaryOnly.FormalObstruction.MixedForms
variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
variable [Fintype ι] [DecidableEq ι]

                                                                              
                                                                                  
theorem separated_parameter_lift_some {b : ℕ}
    (pd : ι → Derivation k A A) (Q p s : Fin b → A) (J : Finset (Fin b))
    (hs : ∀ j i, pd i (s j) = 0) (hs2 : ∀ j, s j * s j = 0)
    (hout : ∀ j ∉ J, s j = 0)
    (x y : Fin b → Forms (k := k) (A := A) (ι := ι))
    (hx : ∀ j, gradient pd (Q j) * x j = 0)
    (hy : ∀ j ∈ J, gradient pd (Q j) * y j = -(gradient pd (p j) * x j)) :
    delta pd (∑ j, (Q j + s j * p j))
      (List.ofFn (fun j => x j + coeff (s j) * y j)).prod = 0 := by
  change gradient pd (∑ j, (Q j + s j * p j)) * _ = 0
  have hg : gradient pd (∑ j, (Q j + s j * p j)) =
      ∑ j, gradient pd (Q j + s j * p j) := by
    change d pd (coeff (k := k) (ι := ι) (∑ j, (Q j + s j * p j))) = _
    rw [map_sum, map_sum]
    rfl
  rw [hg, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro j _
  apply gradient_mul_list_prod_zero pd (Q j + s j * p j)
    _ (x j + coeff (s j) * y j)
  · exact List.mem_ofFn.mpr ⟨j,rfl⟩
  · by_cases hj : j ∈ J
    · exact perturbed_factor pd (Q j) (p j) (s j) (hs j) (hs2 j) (x j) (y j) (hx j) (hy j hj)
    · rw [hout j hj, zero_mul, add_zero, map_zero, zero_mul, add_zero, hx]

end BoundaryOnly.FormalObstruction.MixedForms

namespace BoundaryOnly.FormalObstruction.ActualBlocks
open Frobenius MixedForms
open scoped TensorProduct BigOperators
variable {k : Type*} [Field k] {d : ℕ} {n : Fin d → ℕ}
variable (ell : ℕ) [Fact ell.Prime] [CharP k ell]

def liftScalar (i : Fin d) : Scalar (n := n) (k := k) ell i →ₐ[k]
    ParameterScalar (n := n) (k := k) ell :=
  (baseChange (l := ThreeParameters.Ring k) ell).comp (includeScalar ell i)

def liftBlock (i : Fin d) : Block (n := n) (k := k) ell i →ₐ[k]
    ParameterForms (n := n) (k := k) ell :=
  (coefficientMap (baseChange (l := ThreeParameters.Ring k) ell)).comp (includeBlock ell i)

omit [Fact ell.Prime] in
 theorem liftBlock_delta (i : Fin d) (F : Scalar (n := n) (k := k) ell i)
    (x : Block (n := n) (k := k) ell i) :
    liftBlock ell i (delta (partialDeriv ell) F x) =
      delta (parameterPartial ell) (liftScalar ell i F) (liftBlock ell i x) := by
  simp only [liftBlock, liftScalar, AlgHom.comp_apply]
  rw [← delta_includeBlock]
  exact coefficientMap_delta _ _ _ (baseChange_partial ell) _ _

omit [Fact ell.Prime] [CharP k ell] in
 theorem reduce_liftBlock (i : Fin d) (x : Block (n := n) (k := k) ell i) :
    coefficientMap (reduction ell) (liftBlock ell i x) = includeBlock ell i x := by
  simp only [liftBlock, AlgHom.comp_apply]
  generalize includeBlock ell i x = z
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e => simp only [coefficientMap_tmul, reduction_baseChange]

omit [CharP k ell] in
 theorem liftScalar_potential (D : FormalData (k := k) n) (i : Fin d) :
    liftScalar ell i (blockPotential ell D i) =
      baseChange (l := ThreeParameters.Ring k) ell
        (wallSpecial ell true i (Ideal.Quotient.mk _ (D.P i)) -
          wallSpecial ell false i (Ideal.Quotient.mk _ (D.P i))) := by
  simp only [liftScalar, AlgHom.comp_apply, blockPotential, map_sub, include_wall]

omit [Fact ell.Prime] [CharP k ell] in
 theorem liftScalar_slope (D : FormalData (k := k) n) (i : Fin d) :
    liftScalar ell i (blockSlope ell D i) =
      baseChange (l := ThreeParameters.Ring k) ell (specialSlope ell D true i) := by
  simp only [liftScalar, AlgHom.comp_apply, include_blockSlope]

omit [Fact ell.Prime] [CharP k ell] in
theorem reduction_lifted_product
    (v : Fin d → ParameterScalar (n := n) (k := k) ell)
    (hv : ∀ i, reduction ell (v i) = 0)
    (x y : ∀ i, Block (n := n) (k := k) ell i) :
    coefficientMap (reduction ell)
      (List.ofFn (fun i => liftBlock ell i (x i) + coeff (v i) * liftBlock ell i (y i))).prod =
        (List.ofFn fun i => includeBlock ell i (x i)).prod := by
  rw [map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply]
  rw [map_add, reduce_liftBlock, map_mul, coefficientMap_coeff, hv, map_zero, zero_mul, add_zero]

                                                                           
                                                                            
theorem parameter_cycle (D : FormalData (k := k) n) (J : Finset (Fin d))
    (s : Fin d → ThreeParameters.Ring k)
    (hs : ∀ i, ThreeParameters.augmentation k (s i) = 0)
    (hs2 : ∀ i, s i * s i = 0) (hout : ∀ i ∉ J, s i = 0)
    (x : ∀ i, Block (n := n) (k := k) ell i)
    (hx : ∀ i, delta (partialDeriv ell) (blockPotential ell D i) (x i) = 0)
    (hy : ∀ i ∈ J, ∃ y : Block (n := n) (k := k) ell i,
      delta (partialDeriv ell) (blockPotential ell D i) y =
        -delta (partialDeriv ell) (blockSlope ell D i) (x i)) :
    ∃ beta : ParameterForms (n := n) (k := k) ell,
      delta (parameterPartial ell)
        (movingPotential ell D (firstSlopes s) (firstSlopes_augmentation s hs)) beta = 0 ∧
      coefficientMap (reduction ell) beta = (List.ofFn fun i => includeBlock ell i (x i)).prod := by
  classical
  let y : ∀ i, Block (n := n) (k := k) ell i := fun i =>
    if hi : i ∈ J then Classical.choose (hy i hi) else 0
  have hy' (i : Fin d) (hi : i ∈ J) :
      delta (partialDeriv ell) (blockPotential ell D i) (y i) =
        -delta (partialDeriv ell) (blockSlope ell D i) (x i) := by
    simp only [y, dite_eq_left hi]
    exact Classical.choose_spec (hy i hi)
  let v : Fin d → ParameterScalar (n := n) (k := k) ell :=
    fun i => @algebraMap (ThreeParameters.Ring k) (ParameterScalar (n := n) (k := k) ell)
      inferInstance inferInstance inferInstance (s i)
  let beta := (List.ofFn (fun i => liftBlock ell i (x i) + coeff (v i) * liftBlock ell i (y i))).prod
  refine ⟨beta, ?_, ?_⟩
  · have hc := separated_parameter_lift_some (parameterPartial (n := n) (k := k) ell)
      (fun i => liftScalar ell i (blockPotential ell D i))
      (fun i => liftScalar ell i (blockSlope ell D i)) v J
      (by
        intro i c
        change partialDeriv (k := ThreeParameters.Ring k) ell c
          (algebraMap (ThreeParameters.Ring k) _ (s i)) = 0
        exact Derivation.map_algebraMap _ _)
      (by intro i; dsimp [v]; rw [← map_mul, hs2, map_zero])
      (by intro i hi; dsimp [v]; rw [hout i hi, map_zero])
      (fun i => liftBlock ell i (x i)) (fun i => liftBlock ell i (y i))
      (by
        intro i
        change delta (parameterPartial ell) (liftScalar ell i (blockPotential ell D i))
          (liftBlock ell i (x i)) = 0
        rw [← liftBlock_delta, hx, map_zero])
      (by
        intro i hi
        change delta (parameterPartial ell) (liftScalar ell i (blockPotential ell D i))
          (liftBlock ell i (y i)) =
            -delta (parameterPartial ell) (liftScalar ell i (blockSlope ell D i))
              (liftBlock ell i (x i))
        rw [← liftBlock_delta, ← liftBlock_delta, hy' i hi, map_neg])
    change delta (parameterPartial ell) _ beta = 0 at hc
    rw [movingPotential_first_order ell D s hs hs2]
    simpa only [liftScalar_potential, liftScalar_slope] using hc
  · apply reduction_lifted_product ell v _ x y
    intro i
    change reduction ell (algebraMap (ThreeParameters.Ring k) _ (s i)) = 0
    rw [reduction_base, hs, map_zero]

end BoundaryOnly.FormalObstruction.ActualBlocks

end

end OAI
