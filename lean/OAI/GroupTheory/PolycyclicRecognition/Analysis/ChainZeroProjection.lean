import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexTotalComparison
import Mathlib.Algebra.Homology.SingleHomology

namespace OAI

/-! # The natural degree-zero quotient of an integral chain complex -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits HomologicalComplex

abbrev integralChainZeroFunctor :=
  opcyclesFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 0 ⋙
    ChainComplex.single₀ (ModuleCat ℤ)

def integralChainZeroProjection (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    K ⟶ integralChainZeroFunctor.obj K :=
  (ChainComplex.toSingle₀Equiv K _).symm ⟨K.pOpcycles 0, K.d_pOpcycles 1 0⟩

@[simp]
theorem integralChainZeroProjection_f_zero (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    (integralChainZeroProjection K).f 0 = K.pOpcycles 0 :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

def integralChainZeroNatTrans : 𝟭 (ChainComplex (ModuleCat.{0} ℤ) ℕ) ⟶ integralChainZeroFunctor where
  app := integralChainZeroProjection
  naturality {K L} f := by
    apply (ChainComplex.toSingle₀Equiv K _).injective
    apply Subtype.ext
    change f.f 0 ≫ (integralChainZeroProjection L).f 0 =
      (integralChainZeroProjection K).f 0 ≫ _
    rw [integralChainZeroProjection_f_zero, integralChainZeroProjection_f_zero]
    exact (K.p_opcyclesMap f 0).symm

instance integralChainZeroProjection_epi (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    Epi (integralChainZeroProjection K) := by
  apply HomologicalComplex.epi_of_epi_f
  intro n
  cases n with
  | zero =>
    change Epi (K.pOpcycles 0)
    infer_instance
  | succ n =>
    exact (isZero_single_obj_X (ComplexShape.down ℕ) 0 (K.opcycles 0)
      (n + 1) (by omega)).epi _

theorem integralChainZeroProjection_quasiIsoAt_zero
    (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) : QuasiIsoAt (integralChainZeroProjection K) 0 := by
  have he : opcyclesMap (integralChainZeroProjection K) 0 =
      (singleObjOpcyclesSelfIso (ComplexShape.down ℕ) 0 (K.opcycles 0)).hom := by
    apply (cancel_epi (K.pOpcycles 0)).mp
    erw [K.p_opcyclesMap, integralChainZeroProjection_f_zero]
    rfl
  have : IsIso (opcyclesMap (integralChainZeroProjection K) 0) := by
    exact he.symm ▸ (inferInstance : IsIso
      (singleObjOpcyclesSelfIso (ComplexShape.down ℕ) 0 (K.opcycles 0)).hom)
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : IsIso (K.isoHomologyι₀.inv ≫ homologyMap (integralChainZeroProjection K) 0) := by
    rw [ChainComplex.isoHomologyι₀_inv_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left K.isoHomologyι₀.inv
    (homologyMap (integralChainZeroProjection K) 0)

theorem integralChainZeroProjection_quasiIso (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (hex : ∀ n, K.ExactAt (n + 1)) : QuasiIso (integralChainZeroProjection K) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero => exact integralChainZeroProjection_quasiIsoAt_zero K
  | succ n =>
    apply (quasiIsoAt_iff_exactAt (integralChainZeroProjection K) (n + 1) (hex n)).mpr
    exact exactAt_single_obj (ComplexShape.down ℕ) 0 (K.opcycles 0) (n + 1) (by omega)

end PolycyclicRecognition

end

end OAI
