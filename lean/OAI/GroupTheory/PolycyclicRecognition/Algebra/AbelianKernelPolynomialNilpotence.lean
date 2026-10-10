import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianCyclicPolynomialNilpotence
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGrowthSubgroups
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicKernelPolynomialGrowth
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CharacteristicCyclicSubgroup
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicTorsionFree
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteKernelAscendingBase
import Mathlib.LinearAlgebra.FreeModule.PID

namespace OAI

/-! # Polynomial growth with an abelian kernel and cyclic quotient

The kernel need not be torsion free or initially finitely generated.
Polynomial growth supplies finite generation. A characteristic finite-index
torsion-free subgroup gives an actual finite-index cyclic extension, where
the integral-action argument applies.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative

theorem polynomial_growth_abelian_kernel_virtually_nilpotent
    {G : Type} [Group G] [DecidableEq G]
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (q : G →* Multiplicative ℤ) (hq : Function.Surjective q)
    [IsMulCommutative q.ker] : Group.IsVirtuallyNilpotent G := by
  classical
  let : Group.FG G := Group.fg_def.mpr ⟨S, hgen⟩
  let : Group.FG q.ker := (Group.fg_iff_subgroup_fg q.ker).mpr
    (cyclic_kernel_fg_of_polynomial_growth S hS hgen hvol q hq)
  obtain ⟨L, hLi, hLtf⟩ :=
    (isPolycyclic_of_finitelyGenerated_commGroup q.ker).exists_torsionFree_finiteIndex
  let := hLi
  obtain ⟨K, hKL, hKchar, hKi⟩ := exists_characteristic_finiteIndex_le L
  let := hKchar
  let := hKi
  have hKtf : HasNoNontrivialTorsion K :=
    hLtf.of_injective (Subgroup.inclusion hKL) (Subgroup.inclusion_injective hKL)
  let : IsMulTorsionFree K := isMulTorsionFree_iff_not_isOfFinOrder.mpr (by
    intro a ha hfin
    exact ha (hKtf a (orderOf a) (ne_of_gt hfin.orderOf_pos) (pow_orderOf_eq_one a)))
  let : Module.IsTorsionFree ℤ (Additive K) := inferInstance
  let : Module.Finite ℤ (Additive K) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  obtain ⟨t, ht⟩ := hq (Multiplicative.ofAdd 1)
  let a : MulAut q.ker := MulAut.conjNormal t
  let aK := MulAut.characteristic K a
  let D := K ⋊[integerPowerAction aK] Multiplicative ℤ
  let e := cyclicKernelEquiv q t ht
  let j : D →* G := e.toMonoidHom.comp (characteristicCyclicMap K a)
  have hj : Function.Injective j := e.injective.comp (characteristicCyclicMap_injective K a)
  have hji : j.range.FiniteIndex := by
    rw [MonoidHom.range_comp]
    let := characteristicCyclicMap_finiteIndex K a
    exact Subgroup.FiniteIndex.map_of_surjective (characteristicCyclicMap K a).range e.surjective
  let := hji
  let ej := MulEquiv.ofBijective j.rangeRestrict ⟨by
    intro x y h
    exact hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  let : Group.FG D := Group.fg_of_surjective (f := ej.symm.toMonoidHom) ej.symm.surjective
  obtain ⟨C, d, hvol⟩ := hvol
  obtain ⟨T, hT, hTgen, M, hM⟩ := polynomial_growth_fg_injective
    S hS hgen C d hvol j hj
  let fK : K ≃* Multiplicative (Additive K) :=
    { toFun := fun x => Multiplicative.ofAdd (Additive.ofMul x)
      invFun := fun x => x.toAdd.toMul
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let qD : D →* Multiplicative ℤ := SemidirectProduct.rightHom
  let tD : D := SemidirectProduct.inr (Multiplicative.ofAdd 1)
  let fD := (cyclicSemidirectKernelEquiv aK).symm.trans fK
  have hD : Group.IsVirtuallyNilpotent D :=
    abelian_cyclic_polynomial_growth_virtually_nilpotent T hT hTgen ⟨M, d, hM⟩
      qD tD rfl fD
  have hR : Group.IsVirtuallyNilpotent j.range := by
    obtain ⟨V, hVnil, hVi⟩ := hD
    let := hVnil
    let := hVi
    refine ⟨V.map ej.toMonoidHom, ?_, Subgroup.FiniteIndex.map_of_surjective V ej.surjective⟩
    exact Group.nilpotent_of_surjective
      (V.equivMapOfInjective ej.toMonoidHom ej.injective).toMonoidHom
      (V.equivMapOfInjective ej.toMonoidHom ej.injective).surjective
  exact virtuallyNilpotent_of_finiteIndex j.range hR

end PolycyclicRecognition

end

end OAI
