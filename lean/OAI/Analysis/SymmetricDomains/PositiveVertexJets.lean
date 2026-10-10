import Mathlib
import OAI.Analysis.SymmetricDomains.OneKernel

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
namespace LieAlgebra
open scoped _root_.LieAlgebra
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L] [LieAlgebra ℚ L]

theorem innerExp_apply_of_cube_zero (T : L) (hT : IsNilpotent (LieAlgebra.ad ℂ L T))
    (c : ℂ) (X : L) (hX : ⁅T,⁅T,⁅T,X⁆⁆⁆=0) :
    innerExp T hT c X=X+c • ⁅T,X⁆+(c^2/2) • ⁅T,⁅T,X⁆⁆ := by
  let A := c • LieAlgebra.ad ℂ L T
  have hn : IsNilpotent A := hT.smul c
  have hs : (A^3) • X=0 := by
    change A (A (A X))=0
    simp [A,hX]
  change IsNilpotent.exp A X=_
  have he := IsNilpotent.exp_smul_eq_sum hs hn
  change IsNilpotent.exp A X= _ at he
  rw [he]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,Module.End.one_apply,
    Nat.factorial_zero,Nat.factorial_succ,Module.End.smul_def]
  simp [A,Module.End.pow_apply,smul_smul]
  module
end LieAlgebra

open Filter Topology
open scoped TensorProduct
namespace Release061.Biholomorph.WeightedLieModel
variable {r k : ℕ} {G : Type*} [LieRing G] [LieAlgebra ℝ G]
    (M : WeightedLieModel r k G)

theorem field_euler_value : M.field M.E M.point=Complex.I • M.u := by
  rw [M.euler_germ.eq_of_nhds,map_smul,flatWeightedEuler_normal]

theorem field_translation_value : M.field M.T M.point=M.u :=
  M.translation_germ.eq_of_nhds

theorem field_rotation_value : M.field M.H M.point=0 := by
  rw [M.rotation_germ.eq_of_nhds,map_smul,flatTangentialInfinitesimal_normal,smul_zero]

theorem firstJet_euler : M.firstJet M.E=flatWeightedEuler r k := by
  change fderiv ℂ (M.field M.E) M.point=_
  rw [M.euler_germ.fderiv_eq,(flatWeightedEuler r k).fderiv]

theorem firstJet_translation : M.firstJet M.T=0 := by
  change fderiv ℂ (M.field M.T) M.point=_
  rw [M.translation_germ.fderiv_eq,fderiv_const_apply]

theorem firstJet_rotation : M.firstJet M.H=flatTangentialInfinitesimal r k := by
  change fderiv ℂ (M.field M.H) M.point=_
  rw [M.rotation_germ.fderiv_eq,(flatTangentialInfinitesimal r k).fderiv]

theorem ofReal_smul (c : ℝ) (X : G) :
    Complexification.ofReal (c • X)=(c : ℂ) • Complexification.ofReal X := by
  rw [map_smul]
  exact (IsScalarTower.algebraMap_smul ℂ c (Complexification.ofReal X)).symm

theorem positive_vertex_jets (V : G) (hV : ⁅M.euler,V⁆=V)
    (hTV : ⁅M.translation,⁅M.translation,V⁆⁆=(-2 : ℝ) • M.translation) :
    let W := ⁅M.translation,V⁆+(2 : ℝ) • M.euler
    M.field (Complexification.ofReal W) M.point=0 ∧
    M.field (Complexification.ofReal V) M.point=M.u ∧
    M.firstJet (Complexification.ofReal V)=
      Complex.I • (M.firstJet (Complexification.ofReal W)-(2 : ℂ) • flatWeightedEuler r k) := by
  let := complexificationRatLieAlgebra (G := G)
  let Z := Complexification.ofReal V
  let W := ⁅M.translation,V⁆+(2 : ℝ) • M.euler
  let C := Complexification.ofReal W
  have hZ : ⁅M.E,Z⁆=(1 : ℂ) • Z := by
    simpa only [Complex.ofReal_one,one_smul] using M.ofReal_eigen (μ := 1) (by simpa using hV)
  have hC : C=⁅M.T,Z⁆+(2 : ℂ) • M.E := by
    simp only [C,W,map_add,Complexification.ofReal_lie,ofReal_smul,Complex.ofReal_ofNat]
    rfl
  have hTTZ : ⁅M.T,⁅M.T,Z⁆⁆=(-2 : ℂ) • M.T := by
    rw [←Complexification.ofReal_lie,←Complexification.ofReal_lie,hTV,ofReal_smul]
    norm_num
  have hTC : ⁅M.T,C⁆=0 := by
    rw [hC,LieRing.lie_add,LieAlgebra.lie_smul (2 : ℂ) M.T M.E,M.translation_euler,hTTZ]
    module
  have hEC : ⁅M.E,C⁆=(0 : ℂ) • C := by
    rw [hC,LieRing.lie_add,LieAlgebra.lie_smul (2 : ℂ) M.E M.E,lie_self,smul_zero,add_zero]
    simpa only [sub_self,zero_smul] using M.bracket_translation_eigen hZ
  have hcC : M.center C=C := M.center_of_commutes hTC
  have hCp : M.field C M.point=0 := by
    simpa only [hcC] using M.centered_value_zero hEC (Or.inl rfl)
  have hTTTZ : ⁅M.T,⁅M.T,⁅M.T,Z⁆⁆⁆=0 := by
    rw [hTTZ,LieAlgebra.lie_smul (-2 : ℂ) M.T M.T,lie_self,smul_zero]
  have hcZ : M.center Z=Z-Complex.I • C+(2*Complex.I) • M.E+M.T := by
    rw [center,LieAlgebra.innerExp_apply_of_cube_zero _ _ _ _ hTTTZ,hTTZ]
    rw [hC]
    simp only [smul_add,smul_smul,sub_eq_add_neg]
    norm_num
    module
  have hval : M.field Z M.point=M.u := by
    have hz := M.centered_value_zero hZ (Or.inr (Or.inr rfl))
    rw [hcZ] at hz
    simp only [map_add,map_sub,map_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,
      hCp,M.field_euler_value,M.field_translation_value,smul_zero,sub_zero,smul_smul] at hz
    rw [mul_assoc,Complex.I_mul_I,mul_neg_one] at hz
    apply sub_eq_zero.mp
    calc
      M.field Z M.point-M.u = M.field Z M.point+(-2 : ℂ) • M.u+M.u := by module
      _=0 := hz
  have hder : M.firstJet Z=Complex.I • (M.firstJet C-(2 : ℂ) • flatWeightedEuler r k) := by
    have hz := M.centered_firstJet_one_zero hZ
    rw [hcZ] at hz
    simp only [map_add,map_sub,map_smul,M.firstJet_euler,M.firstJet_translation,add_zero] at hz
    apply sub_eq_zero.mp
    calc
      M.firstJet Z-Complex.I • (M.firstJet C-(2 : ℂ) • flatWeightedEuler r k) =
        M.firstJet Z-Complex.I • M.firstJet C+(2*Complex.I) • flatWeightedEuler r k := by module
      _=0 := hz
  exact ⟨hCp,hval,hder⟩

end Release061.Biholomorph.WeightedLieModel

end

end OAI
